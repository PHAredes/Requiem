#define _POSIX_C_SOURCE 199309L
#include <janet.h>
#include <stdint.h>
#include <time.h>

static inline uint64_t t_now() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}
static const char *t_type = "nanoseconds";

static Janet cf_now(int32_t argc, Janet *argv) {
    (void)argc; (void)argv; 
    uint64_t ns = t_now();
    return janet_wrap_number((double)ns);
}

static Janet cf_ms(int32_t argc, Janet *argv) {
    (void)argc; (void)argv; 
    uint64_t ns = t_now();
    return janet_wrap_number((double)ns / 1000000.0);
}

static Janet cf_type(int32_t argc, Janet *argv) {
    (void)argc; (void)argv; return janet_wrap_string(janet_cstring(t_type));
}

static const JanetReg reg[] = {
    {"now", cf_now, NULL}, 
    {"ms", cf_ms, NULL}, 
    {"type", cf_type, NULL}, 
    {NULL, NULL, NULL}
};

JANET_MODULE_ENTRY(JanetTable *env) { janet_cfuns(env, "timer", reg); }
