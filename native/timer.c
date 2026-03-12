#define _POSIX_C_SOURCE 200112L
#include <janet.h>
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#ifndef CLOCK_MONOTONIC
#error "timer requires CLOCK_MONOTONIC"
#endif

#define T_NS_PER_SEC 1000000000LL
#define T_NS_PER_MS 1000000.0

static const char *t_clock_type = "monotonic";
static const char *t_now_type = "s64";
static const char *t_ms_type = "number";
static const char *t_now_unit = "ns";
static const char *t_ms_unit = "ms";

static Janet t_clockv(void) {
    return janet_cstringv(t_clock_type);
}

static inline int64_t t_now(void) {
    struct timespec ts;
    errno = 0;
    if (clock_gettime(CLOCK_MONOTONIC, &ts)) {
        janet_panicf("timer: clock_gettime(CLOCK_MONOTONIC) failed: %s", strerror(errno));
    }
    if (ts.tv_sec < 0 || ts.tv_nsec < 0 || ts.tv_nsec >= T_NS_PER_SEC) {
        janet_panic("timer: clock_gettime(CLOCK_MONOTONIC) returned an invalid timespec");
    }
    if ((uint64_t) ts.tv_sec > (uint64_t) (INT64_MAX / T_NS_PER_SEC)) {
        janet_panic("timer: monotonic clock value overflowed int64 nanoseconds");
    }
    return ((int64_t) ts.tv_sec * T_NS_PER_SEC) + (int64_t) ts.tv_nsec;
}

static const char *t_type_for(const char *query) {
    if (!query || !strcmp(query, "now")) return t_now_type;
    if (!strcmp(query, "ms")) return t_ms_type;
    janet_panicf("timer: unsupported type query '%s' (expected now or ms)", query);
    return NULL;
}

static const char *t_unit_for(const char *query) {
    if (!query || !strcmp(query, "now")) return t_now_unit;
    if (!strcmp(query, "ms")) return t_ms_unit;
    janet_panicf("timer: unsupported unit query '%s' (expected now or ms)", query);
    return NULL;
}

static Janet cf_clock(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 0);
    (void) argc;
    (void) argv;
    return t_clockv();
}

static Janet cf_now(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 0);
    (void) argc;
    (void) argv;
    return janet_wrap_s64(t_now());
}

static Janet cf_ms(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 0);
    (void) argc;
    (void) argv;
    return janet_wrap_number((double) t_now() / T_NS_PER_MS);
}

static Janet cf_type(int32_t argc, Janet *argv) {
    janet_arity(argc, 0, 1);
    return janet_cstringv(t_type_for(argc ? janet_getcstring(argv, 0) : NULL));
}

static Janet cf_unit(int32_t argc, Janet *argv) {
    janet_arity(argc, 0, 1);
    return janet_cstringv(t_unit_for(argc ? janet_getcstring(argv, 0) : NULL));
}

static const JanetReg reg[] = {
    {"clock", cf_clock, "(timer/clock)\n\nReturn the clock source used by the timer module."},
    {"now", cf_now, "(timer/now)\n\nReturn monotonic time in nanoseconds as an exact signed 64-bit integer."},
    {"ms", cf_ms, "(timer/ms)\n\nReturn monotonic time in milliseconds as a Janet number."},
    {"type", cf_type, "(timer/type &opt query)\n\nReport the value type for timer readings. Query is one of nil/\"now\" or \"ms\"."},
    {"unit", cf_unit, "(timer/unit &opt query)\n\nReport the unit used by timer readings. Query is one of nil/\"now\" or \"ms\"."},
    {NULL, NULL, NULL}
};

JANET_MODULE_ENTRY(JanetTable *env) { janet_cfuns(env, "timer", reg); }
