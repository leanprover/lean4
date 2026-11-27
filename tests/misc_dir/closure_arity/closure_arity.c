/* Check closure and application-count boundaries with release assertions disabled. */
#include <lean/lean.h>

int printf(char const * fmt, ...);
void lean_initialize_runtime_module(void);

static unsigned failures = 0;
static unsigned array_arity;

static void check(bool condition) {
    if (!condition) ++failures;
}

static lean_object * array_fun(lean_object ** args) {
    for (unsigned i = 0; i < array_arity - 2; ++i) check(lean_unbox(args[i]) == 7);
    check(lean_unbox(args[array_arity - 2]) == 11);
    return args[array_arity - 1];
}

static lean_object * small_fun(lean_object * a, lean_object * b) {
    check(lean_unbox(a) == 7);
    return b;
}

static lean_object * small_closure(void) {
    lean_object * f = lean_alloc_closure((void *)small_fun, 2, 1);
    lean_closure_set(f, 0, lean_box(7));
    return f;
}

static void check_valid(void) {
    check(lean_unbox(lean_apply_1(small_closure(), lean_box(12))) == 12);
    lean_object * empty = lean_alloc_closure((void *)array_fun, UINT16_MAX, 0);
    check(lean_closure_arity(empty) == UINT16_MAX && lean_closure_num_fixed(empty) == 0);
    lean_dec(empty);
    unsigned arities[] = {LEAN_CLOSURE_MAX_ARGS + 1, UINT16_MAX};
    for (unsigned j = 0; j < 2; ++j) {
        array_arity = arities[j];
        for (unsigned shared = 0; shared < 2; ++shared) {
            lean_object * f = lean_alloc_closure((void *)array_fun, array_arity, array_arity - 2);
            for (unsigned i = 0; i < array_arity - 2; ++i) lean_closure_set(f, i, lean_box(7));
            if (shared) lean_inc(f);
            lean_object * partial = lean_apply_1(f, lean_box(11));
            check(lean_closure_arity(partial) == array_arity);
            check(lean_closure_num_fixed(partial) == array_arity - 1);
            check(lean_unbox(lean_apply_1(partial, lean_box(12))) == 12);
            if (shared) lean_dec(f);
        }
    }
    /* The largest supported argument vector can still overapply a small closure. */
    lean_object * args[UINT16_MAX];
    for (unsigned i = 0; i < UINT16_MAX; ++i) args[i] = lean_box(12);
    check(lean_unbox(lean_apply_m(small_closure(), UINT16_MAX, args)) == 12);
    check(lean_unbox(lean_apply_n(small_closure(), UINT16_MAX, args)) == 12);
}

int main(int argc, char ** argv) {
    lean_initialize_runtime_module();
    if (argc == 1) {
        check_valid();
        if (failures) printf("%u closure checks failed\n", failures);
        return failures != 0;
    }
    switch (argv[1][0]) {
    case 'a': lean_alloc_closure((void *)array_fun, UINT16_MAX + 1u, 0); break;
    case 'b': lean_alloc_closure((void *)array_fun, UINT16_MAX + 2u, UINT16_MAX + 1u); break;
    case 'c': lean_alloc_closure((void *)array_fun, UINT_MAX, 0); break;
    case 'z': lean_alloc_closure((void *)array_fun, 0, 0); break;
    case 'f': lean_alloc_closure((void *)small_fun, 2, 2); break;
    case 'g': lean_alloc_closure((void *)small_fun, 2, UINT_MAX); break;
    /* Oversized counts must be rejected before reading the argument vector. */
    case 'm': lean_apply_m(small_closure(), UINT_MAX, NULL); break;
    case 'n': lean_apply_n(small_closure(), UINT_MAX, NULL); break;
    case 'p': lean_apply_m(small_closure(), UINT16_MAX + 1u, NULL); break;
    case 'q': lean_apply_n(small_closure(), UINT16_MAX + 1u, NULL); break;
    case 's': lean_apply_n(lean_box(0), UINT_MAX, NULL); break;
    }
    printf("accepted an unsupported closure or application count\n");
    return 1;
}
