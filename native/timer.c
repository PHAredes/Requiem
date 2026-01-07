#include <janet.h>
#include <stdint.h>
#include <time.h>

#ifdef __x86_64__
static inline uint64_t t_now() {
    uint32_t l, h;
    __asm__ __volatile__ ("rdtsc" : "=a" (l), "=d" (h));
    return ((uint64_t)h << 32) | l;
}
static const char *t_type = "cycles";
#else
static inline uint64_t t_now() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}
static const char *t_type = "nanoseconds";
#endif

static Janet cf_now(int32_t argc, Janet *argv) {
    (void)argc; (void)argv; return janet_wrap_number((double)t_now());
}

static Janet cf_type(int32_t argc, Janet *argv) {
    (void)argc; (void)argv; return janet_wrap_string(janet_cstring(t_type));
}

static const JanetReg reg[] = {
    {"now", cf_now, NULL}, {"type", cf_type, NULL}, {NULL, NULL, NULL}
};

JANET_MODULE_ENTRY(JanetTable *env) { janet_cfuns(env, "timer", reg); }
