#include <janet.h>
#include <stdio.h>
#include <stdlib.h>
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

#define T_INODE 0
#define T_FULL  1
#define T_NIL   3
#define T_TRUE  5
#define T_FALSE 7
#define T_MASK  7

static inline bool is_leaf(void *p) { return ((uintptr_t)p & 1) != 0; }
static inline bool is_full(void *p) { return ((uintptr_t)p & T_MASK) == T_FULL; }
static inline void *get_key(void *p) { return (void *)((uintptr_t)p & ~T_MASK); }

static Janet get_val(void *p) {
    uintptr_t t = (uintptr_t)p & T_MASK;
    if (t == T_TRUE) return janet_wrap_true();
    if (t == T_FALSE) return janet_wrap_false();
    return janet_wrap_nil();
}

static int can_inline(Janet v, uintptr_t *t) {
    if (janet_checktype(v, JANET_NIL)) { *t = T_NIL; return 1; }
    if (janet_checktype(v, JANET_BOOLEAN)) { *t = janet_unwrap_boolean(v) ? T_TRUE : T_FALSE; return 1; }
    return 0;
}

#define A_CHUNK (64 * 1024)

typedef struct AChunk { struct AChunk *next; } AChunk;
typedef struct { uint32_t rc; AChunk *chunks; char *curr, *end; } HArena;

static HArena *a_new() {
    HArena *a = janet_malloc(sizeof(HArena));
    a->rc = 1; a->chunks = NULL; a->curr = a->end = NULL;
    return a;
}

static void *a_alloc(HArena *a, size_t sz) {
    sz = (sz + 7) & ~7;
    if (a->curr + sz > a->end) {
        size_t csz = sz > A_CHUNK ? sz : A_CHUNK;
        AChunk *c = janet_malloc(sizeof(AChunk) + csz);
        c->next = a->chunks; a->chunks = c;
        a->curr = (char *)(c + 1); a->end = a->curr + csz;
    }
    void *p = a->curr; a->curr += sz;
    return p;
}

static void a_inc(HArena *a) { if (a) a->rc++; }
static void a_dec(HArena *a) {
    if (!a || --a->rc > 0) return;
    AChunk *c = a->chunks;
    while (c) { AChunk *n = c->next; janet_free(c); c = n; }
    janet_free(a);
}

static char *a_dup(HArena *a, const char *s) {
    size_t l = strlen(s) + 1;
    char *d = a_alloc(a, l); memcpy(d, s, l);
    return d;
}

typedef struct { uint32_t bits; void *kids[]; } HFam;
typedef struct { char *key; Janet val; } LFam;

static LFam *l_fam_new(HArena *a, const char *k, Janet v) {
    LFam *l = a_alloc(a, sizeof(LFam)); l->key = a_dup(a, k); l->val = v;
    return l;
}

static HFam *n_fam_new(HArena *a, uint32_t b, int c) {
    HFam *n = a_alloc(a, sizeof(HFam) + (c * sizeof(void *))); n->bits = b;
    return n;
}

typedef struct { uint32_t bits; void **kids; } HMut;
typedef struct { char *key; Janet val; } LMut;

static LMut *l_mut_new(HArena *a, const char *k, Janet v) {
    LMut *l = a_alloc(a, sizeof(LMut)); l->key = a_dup(a, k); l->val = v;
    return l;
}

static HMut *n_mut_new(HArena *a) {
    HMut *n = a_alloc(a, sizeof(HMut)); n->bits = 0; n->kids = NULL;
    return n;
}

static inline void *mk_l_fam(HArena *a, const char *k, Janet v) {
    uintptr_t t;
    if (can_inline(v, &t)) return (void *)((uintptr_t)a_dup(a, k) | t);
    return (void *)((uintptr_t)l_fam_new(a, k, v) | T_FULL);
}

static inline void *mk_l_mut(HArena *a, const char *k, Janet v) {
    uintptr_t t;
    if (can_inline(v, &t)) return (void *)((uintptr_t)a_dup(a, k) | t);
    return (void *)((uintptr_t)l_mut_new(a, k, v) | T_FULL);
}

static int h_get_fam(void *n, const char *k, uint64_t h, int d, Janet *o) {
    if (!n) return 0;
    if (is_leaf(n)) {
        char *lk;
        if (is_full(n)) { LFam *l = (LFam *)get_key(n); lk = l->key; if (!strcmp(lk, k)) { *o = l->val; return 1; } }
        else { lk = (char *)get_key(n); if (!strcmp(lk, k)) { *o = get_val(n); return 1; } }
        return 0;
    }
    HFam *in = (HFam *)n; uint32_t idx = h_frag(h, d);
    if (!(in->bits & (1u << idx))) return 0;
    int p = (in->bits == 0xFFFFFFFF) ? idx : h_pop(in->bits & ((1u << idx) - 1));
    return h_get_fam(in->kids[p], k, h, d + 1, o);
}

static int h_get_mut(void *n, const char *k, uint64_t h, int d, Janet *o) {
    if (!n) return 0;
    if (is_leaf(n)) {
        char *lk;
        if (is_full(n)) { LMut *l = (LMut *)get_key(n); lk = l->key; if (!strcmp(lk, k)) { *o = l->val; return 1; } }
        else { lk = (char *)get_key(n); if (!strcmp(lk, k)) { *o = get_val(n); return 1; } }
        return 0;
    }
    HMut *in = (HMut *)n; uint32_t idx = h_frag(h, d);
    if (!(in->bits & (1u << idx))) return 0;
    int p = (in->bits == 0xFFFFFFFF) ? idx : h_pop(in->bits & ((1u << idx) - 1));
    return h_get_mut(in->kids[p], k, h, d + 1, o);
}

static void *h_freeze(HArena *a, void *n) {
    if (!n) return NULL;
    if (is_leaf(n)) {
        if (is_full(n)) { LMut *l = (LMut *)get_key(n); return mk_l_fam(a, l->key, l->val); }
        else { char *k = (char *)get_key(n); return (void *)((uintptr_t)a_dup(a, k) | ((uintptr_t)n & T_MASK)); }
    }
    HMut *in = (HMut *)n; int c = h_pop(in->bits);
    HFam *nf = n_fam_new(a, in->bits, c);
    for (int i = 0; i < c; i++) nf->kids[i] = h_freeze(a, in->kids[i]);
    return nf;
}

static void *h_put_fam(HArena *a, void *n, const char *k, Janet v, uint64_t h, int d, bool *add) {
    if (!n) { *add = true; return mk_l_fam(a, k, v); }
    if (is_leaf(n)) {
        char *lk; Janet lv;
        if (is_full(n)) { LFam *l = (LFam *)get_key(n); lk = l->key; lv = l->val; }
        else { lk = (char *)get_key(n); lv = get_val(n); }
        if (!strcmp(lk, k)) { *add = false; return mk_l_fam(a, k, v); }
        *add = true; uint64_t ho = h_hash(lk); uint32_t io = h_frag(ho, d), in = h_frag(h, d);
        if (io == in) {
            HFam *nf = n_fam_new(a, 1u << io, 1);
            nf->kids[0] = h_put_fam(a, n, k, v, h, d + 1, add); return nf;
        } else {
            HFam *nf = n_fam_new(a, (1u << io) | (1u << in), 2);
            void *l1 = mk_l_fam(a, lk, lv), *l2 = mk_l_fam(a, k, v);
            if (io < in) { nf->kids[0] = l1; nf->kids[1] = l2; } else { nf->kids[0] = l2; nf->kids[1] = l1; }
            return nf;
        }
    }
    HFam *in = (HFam *)n; uint32_t idx = h_frag(h, d), bit = 1u << idx;
    int p = h_pop(in->bits & (bit - 1)), c = h_pop(in->bits);
    if (in->bits & bit) {
        HFam *nf = n_fam_new(a, in->bits, c); memcpy(nf->kids, in->kids, c * sizeof(void *));
        nf->kids[p] = h_put_fam(a, nf->kids[p], k, v, h, d + 1, add); return nf;
    } else {
        HFam *nf = n_fam_new(a, in->bits | bit, c + 1);
        memcpy(nf->kids, in->kids, p * sizeof(void *)); nf->kids[p] = mk_l_fam(a, k, v);
        memcpy(nf->kids + p + 1, in->kids + p, (c - p) * sizeof(void *)); return nf;
    }
}

static void *h_put_mut(HArena *a, void *n, const char *k, Janet v, uint64_t h, int d, bool *ins) {
    if (!n) { *ins = true; return mk_l_mut(a, k, v); }
    if (is_leaf(n)) {
        char *lk; Janet lv;
        if (is_full(n)) { LMut *l = (LMut *)get_key(n); lk = l->key; lv = l->val; }
        else { lk = (char *)get_key(n); lv = get_val(n); }
        if (!strcmp(lk, k)) {
            uintptr_t t;
            if (can_inline(v, &t)) { *ins = false; return (void *)((uintptr_t)lk | t); }
            if (!is_full(n)) { *ins = false; return (void *)((uintptr_t)l_mut_new(a, lk, v) | T_FULL); }
            LMut *l = (LMut *)get_key(n); l->val = v; *ins = false; return n;
        }
        HMut *nf = n_mut_new(a); uint64_t ho = h_hash(lk); uint32_t io = h_frag(ho, d), in = h_frag(h, d);
        if (io == in) {
            nf->bits = 1u << io; nf->kids = a_alloc(a, sizeof(void *));
            void *sub = h_put_mut(a, NULL, lk, lv, ho, d + 1, ins);
            nf->kids[0] = h_put_mut(a, sub, k, v, h, d + 1, ins);
        } else {
            nf->bits = (1u << io) | (1u << in); nf->kids = a_alloc(a, 2 * sizeof(void *));
            void *l1 = mk_l_mut(a, lk, lv), *l2 = mk_l_mut(a, k, v);
            if (io < in) { nf->kids[0] = l1; nf->kids[1] = l2; } else { nf->kids[0] = l2; nf->kids[1] = l1; }
            *ins = true;
        }
        return nf;
    }
    HMut *in = (HMut *)n; uint32_t idx = h_frag(h, d), bit = 1u << idx;
    if (in->bits & bit) {
        int p = (in->bits == 0xFFFFFFFF) ? idx : h_pop(in->bits & (bit - 1));
        in->kids[p] = h_put_mut(a, in->kids[p], k, v, h, d + 1, ins);
    } else {
        int c = h_pop(in->bits), p = h_pop(in->bits & (bit - 1));
        void **nk = a_alloc(a, (c + 1) * sizeof(void *));
        memcpy(nk, in->kids, p * sizeof(void *)); nk[p] = mk_l_mut(a, k, v);
        memcpy(nk + p + 1, in->kids + p, (c - p) * sizeof(void *));
        in->kids = nk; in->bits |= bit; *ins = true;
    }
    return n;
}

typedef struct { void *root; size_t sz; HArena *a; } Hamt;
static int h_gc(void *p, size_t l) { (void)l; a_dec(((Hamt *)p)->a); return 0; }
static const JanetAbstractType h_fam_t = { "h_fam", h_gc }, h_mut_t = { "h_mut", h_gc };

static Janet cf_fam_new(int32_t argc, Janet *argv) {
    (void)argc; (void)argv; Hamt *h = janet_abstract(&h_fam_t, sizeof(Hamt));
    h->a = a_new(); h->root = NULL; h->sz = 0; return janet_wrap_abstract(h);
}
static Janet cf_mut_new(int32_t argc, Janet *argv) {
    (void)argc; (void)argv; Hamt *h = janet_abstract(&h_mut_t, sizeof(Hamt));
    h->a = a_new(); h->root = NULL; h->sz = 0; return janet_wrap_abstract(h);
}

static Janet cf_mut_put(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 3); Hamt *h = janet_getabstract(argv, 0, &h_mut_t);
    const char *k = janet_getcstring(argv, 1); bool ins = false;
    h->root = h_put_mut(h->a, h->root, k, argv[2], h_hash(k), 0, &ins);
    if (ins) h->sz++; return argv[0];
}

static Janet cf_fam_put(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 3); Hamt *oh = janet_getabstract(argv, 0, &h_fam_t);
    const char *k = janet_getcstring(argv, 1); Hamt *nh = janet_abstract(&h_fam_t, sizeof(Hamt));
    nh->a = oh->a; a_inc(nh->a); bool add = false;
    nh->root = h_put_fam(nh->a, oh->root, k, argv[2], h_hash(k), 0, &add);
    nh->sz = oh->sz + (add ? 1 : 0); return janet_wrap_abstract(nh);
}

static Janet cf_mut_get(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 2); Hamt *h = janet_getabstract(argv, 0, &h_mut_t);
    const char *k = janet_getcstring(argv, 1); Janet v;
    return h_get_mut(h->root, k, h_hash(k), 0, &v) ? v : janet_wrap_nil();
}

static Janet cf_fam_get(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 2); Hamt *h = janet_getabstract(argv, 0, &h_fam_t);
    const char *k = janet_getcstring(argv, 1); Janet v;
    return h_get_fam(h->root, k, h_hash(k), 0, &v) ? v : janet_wrap_nil();
}

static void h_f_coll(void *n, JanetTable *t, JanetArray *ks) {
    if (!n) return;
    if (is_leaf(n)) {
        char *lk; Janet lv;
        if (is_full(n)) { LFam *l = (LFam *)get_key(n); lk = l->key; lv = l->val; }
        else { lk = (char *)get_key(n); lv = get_val(n); }
        Janet k = janet_wrap_string(janet_cstring(lk));
        if (t) janet_table_put(t, k, lv); if (ks) janet_array_push(ks, k); return;
    }
    HFam *in = (HFam *)n; int c = h_pop(in->bits);
    for (int i = 0; i < c; i++) h_f_coll(in->kids[i], t, ks);
}

static void h_m_coll(void *n, JanetTable *t, JanetArray *ks) {
    if (!n) return;
    if (is_leaf(n)) {
        char *lk; Janet lv;
        if (is_full(n)) { LMut *l = (LMut *)get_key(n); lk = l->key; lv = l->val; }
        else { lk = (char *)get_key(n); lv = get_val(n); }
        Janet k = janet_wrap_string(janet_cstring(lk));
        if (t) janet_table_put(t, k, lv); if (ks) janet_array_push(ks, k); return;
    }
    HMut *in = (HMut *)n; int c = h_pop(in->bits);
    for (int i = 0; i < c; i++) h_m_coll(in->kids[i], t, ks);
}

static Janet cf_len(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1);
    Hamt *h = janet_getabstract(argv, 0, janet_abstract_type(janet_unwrap_abstract(argv[0])));
    return janet_wrap_number((double)h->sz);
}

static Janet cf_keys(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1); const JanetAbstractType *at = janet_abstract_type(janet_unwrap_abstract(argv[0]));
    Hamt *h = janet_getabstract(argv, 0, at); JanetArray *ks = janet_array(h->sz);
    if (at == &h_mut_t) h_m_coll(h->root, NULL, ks); else h_f_coll(h->root, NULL, ks);
    return janet_wrap_array(ks);
}

static Janet cf_to_tab(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1); const JanetAbstractType *at = janet_abstract_type(janet_unwrap_abstract(argv[0]));
    Hamt *h = janet_getabstract(argv, 0, at); JanetTable *t = janet_table(h->sz);
    if (at == &h_mut_t) h_m_coll(h->root, t, NULL); else h_f_coll(h->root, t, NULL);
    return janet_wrap_table(t);
}

static Janet cf_freeze(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1); Hamt *hm = janet_getabstract(argv, 0, &h_mut_t), *hf = janet_abstract(&h_fam_t, sizeof(Hamt));
    hf->a = hm->a; a_inc(hf->a); hf->root = h_freeze(hf->a, hm->root); hf->sz = hm->sz;
    return janet_wrap_abstract(hf);
}

static const JanetReg reg[] = {
    {"new-fam", cf_fam_new, NULL}, {"new-mut", cf_mut_new, NULL},
    {"put-mut", cf_mut_put, NULL}, {"get-mut", cf_mut_get, NULL},
    {"put-fam", cf_fam_put, NULL}, {"get-fam", cf_fam_get, NULL},
    {"freeze", cf_freeze, NULL}, {"len", cf_len, NULL},
    {"keys", cf_keys, NULL}, {"to-table", cf_to_tab, NULL}, {NULL, NULL, NULL}
};

JANET_MODULE_ENTRY(JanetTable *env) { janet_cfuns(env, "hamt", reg); }