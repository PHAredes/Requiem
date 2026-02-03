/* Persistent HAMT (Hash Array Mapped Trie) for Janet
 * Functional/immutable variant only - put returns new HAMT
 */
#include <janet.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

#define BITS 5
#define MASK ((1 << BITS) - 1)

static inline uint64_t h_hash(const char *key) {
    uint64_t h = 0xcbf29ce484222325ULL;
    while (*key) { h ^= (unsigned char)*key++; h *= 0x100000001b3ULL; }
    return h;
}

static inline int h_pop(uint32_t x) { return __builtin_popcount(x); }
static inline uint32_t h_frag(uint64_t h, int d) { return (h >> ((d * BITS) % 60)) & MASK; }

/* Pointer tagging: LSB 1 = Leaf, 0 = Node */
#define T_LEAF  1

static inline bool is_leaf(void *p) { return ((uintptr_t)p & T_LEAF) != 0; }
static inline void *get_ptr(void *p) { return (void *)((uintptr_t)p & ~T_LEAF); }

/* Arena allocator */
#define ARENA_CHUNK (64 * 1024)

typedef struct Chunk { struct Chunk *next; } Chunk;
typedef struct { uint32_t rc; Chunk *chunks; char *curr, *end; } Arena;

static Arena *arena_new(void) {
    Arena *a = janet_malloc(sizeof(Arena));
    a->rc = 1; a->chunks = NULL; a->curr = a->end = NULL;
    return a;
}

static void *arena_alloc(Arena *a, size_t sz) {
    sz = (sz + 7) & ~7;
    if (a->curr + sz > a->end) {
        size_t csz = sz > ARENA_CHUNK ? sz : ARENA_CHUNK;
        Chunk *c = janet_malloc(sizeof(Chunk) + csz);
        c->next = a->chunks; a->chunks = c;
        a->curr = (char *)(c + 1); a->end = a->curr + csz;
    }
    void *p = a->curr; a->curr += sz;
    return p;
}

static void arena_inc(Arena *a) { if (a) a->rc++; }
static void arena_dec(Arena *a) {
    if (!a || --a->rc > 0) return;
    Chunk *c = a->chunks;
    while (c) { Chunk *n = c->next; janet_free(c); c = n; }
    janet_free(a);
}

static char *arena_strdup(Arena *a, const char *s) {
    size_t l = strlen(s) + 1;
    char *d = arena_alloc(a, l); memcpy(d, s, l);
    return d;
}

/* Node structures */
typedef struct { uint32_t bits; void *kids[]; } Node;
typedef struct { char *key; Janet val; } Leaf;

static Leaf *leaf_new(Arena *a, const char *k, Janet v) {
    Leaf *l = arena_alloc(a, sizeof(Leaf));
    l->key = arena_strdup(a, k); l->val = v;
    return l;
}

static Node *node_new(Arena *a, uint32_t bits, int count) {
    Node *n = arena_alloc(a, sizeof(Node) + count * sizeof(void *));
    n->bits = bits;
    return n;
}

static inline void *mk_leaf(Arena *a, const char *k, Janet v) {
    return (void *)((uintptr_t)leaf_new(a, k, v) | T_LEAF);
}

/* Core operations */
static int h_get(void *n, const char *k, uint64_t h, int d, Janet *out) {
    if (!n) return 0;
    if (is_leaf(n)) {
        Leaf *l = get_ptr(n);
        if (!strcmp(l->key, k)) { *out = l->val; return 1; }
        return 0;
    }
    Node *node = n; uint32_t idx = h_frag(h, d);
    if (!(node->bits & (1u << idx))) return 0;
    int pos = (node->bits == 0xFFFFFFFF) ? idx : h_pop(node->bits & ((1u << idx) - 1));
    return h_get(node->kids[pos], k, h, d + 1, out);
}

static void *h_put(Arena *a, void *n, const char *k, Janet v, uint64_t h, int d, bool *added) {
    if (!n) { *added = true; return mk_leaf(a, k, v); }
    
    if (is_leaf(n)) {
        Leaf *ol = get_ptr(n);
        if (!strcmp(ol->key, k)) { *added = false; return mk_leaf(a, k, v); }
        
        *added = true;
        char *lk = ol->key; Janet lv = ol->val;
        uint64_t ho = h_hash(lk);
        uint32_t io = h_frag(ho, d), in = h_frag(h, d);
        
        if (io == in) {
            Node *nn = node_new(a, 1u << io, 1);
            nn->kids[0] = h_put(a, n, k, v, h, d + 1, added);
            return nn;
        } else {
            Node *nn = node_new(a, (1u << io) | (1u << in), 2);
            void *l1 = mk_leaf(a, lk, lv), *l2 = mk_leaf(a, k, v);
            if (io < in) { nn->kids[0] = l1; nn->kids[1] = l2; }
            else { nn->kids[0] = l2; nn->kids[1] = l1; }
            return nn;
        }
    }
    
    Node *node = n;
    uint32_t idx = h_frag(h, d), bit = 1u << idx;
    int pos = h_pop(node->bits & (bit - 1)), count = h_pop(node->bits);
    
    if (node->bits & bit) {
        Node *nn = node_new(a, node->bits, count);
        memcpy(nn->kids, node->kids, count * sizeof(void *));
        nn->kids[pos] = h_put(a, nn->kids[pos], k, v, h, d + 1, added);
        return nn;
    } else {
        Node *nn = node_new(a, node->bits | bit, count + 1);
        memcpy(nn->kids, node->kids, pos * sizeof(void *));
        nn->kids[pos] = mk_leaf(a, k, v);
        memcpy(nn->kids + pos + 1, node->kids + pos, (count - pos) * sizeof(void *));
        *added = true;
        return nn;
    }
}

static void h_collect(void *n, JanetTable *t, JanetArray *keys) {
    if (!n) return;
    if (is_leaf(n)) {
        Leaf *l = get_ptr(n);
        Janet k = janet_wrap_string(janet_cstring(l->key));
        if (t) janet_table_put(t, k, l->val);
        if (keys) janet_array_push(keys, k);
        return;
    }
    Node *node = n; int c = h_pop(node->bits);
    for (int i = 0; i < c; i++) h_collect(node->kids[i], t, keys);
}

/* Janet abstract type */
typedef struct { void *root; size_t size; Arena *arena; } Hamt;

static int hamt_gc(void *p, size_t sz) {
    (void)sz; arena_dec(((Hamt *)p)->arena);
    return 0;
}

static const JanetAbstractType hamt_type = { "hamt", hamt_gc };

/* Janet API */
static Janet cf_new(int32_t argc, Janet *argv) {
    (void)argc; (void)argv;
    Hamt *h = janet_abstract(&hamt_type, sizeof(Hamt));
    h->arena = arena_new(); h->root = NULL; h->size = 0;
    return janet_wrap_abstract(h);
}

static Janet cf_put(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 3);
    Hamt *old = janet_getabstract(argv, 0, &hamt_type);
    const char *k = janet_getcstring(argv, 1);
    
    Hamt *new = janet_abstract(&hamt_type, sizeof(Hamt));
    new->arena = old->arena; arena_inc(new->arena);
    
    bool added = false;
    new->root = h_put(new->arena, old->root, k, argv[2], h_hash(k), 0, &added);
    new->size = old->size + (added ? 1 : 0);
    
    return janet_wrap_abstract(new);
}

static Janet cf_get(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 2);
    Hamt *h = janet_getabstract(argv, 0, &hamt_type);
    const char *k = janet_getcstring(argv, 1);
    Janet v;
    return h_get(h->root, k, h_hash(k), 0, &v) ? v : janet_wrap_nil();
}

static Janet cf_len(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1);
    Hamt *h = janet_getabstract(argv, 0, &hamt_type);
    return janet_wrap_number((double)h->size);
}

static Janet cf_keys(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1);
    Hamt *h = janet_getabstract(argv, 0, &hamt_type);
    JanetArray *keys = janet_array(h->size);
    h_collect(h->root, NULL, keys);
    return janet_wrap_array(keys);
}

static Janet cf_to_table(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1);
    Hamt *h = janet_getabstract(argv, 0, &hamt_type);
    JanetTable *t = janet_table(h->size);
    h_collect(h->root, t, NULL);
    return janet_wrap_table(t);
}

static const JanetReg cfuns[] = {
    {"new", cf_new, "(hamt/new)\n\nCreate empty HAMT."},
    {"put", cf_put, "(hamt/put h key val)\n\nReturn new HAMT with key set to val."},
    {"get", cf_get, "(hamt/get h key)\n\nGet value for key, or nil."},
    {"len", cf_len, "(hamt/len h)\n\nReturn number of entries."},
    {"keys", cf_keys, "(hamt/keys h)\n\nReturn array of keys."},
    {"to-table", cf_to_table, "(hamt/to-table h)\n\nConvert to Janet table."},
    {NULL, NULL, NULL}
};

JANET_MODULE_ENTRY(JanetTable *env) { janet_cfuns(env, "hamt", cfuns); }
