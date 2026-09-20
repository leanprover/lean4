/* Deletion cascades must preserve persistent and sticky reference counts. */
#include <stdio.h>
#include <lean/lean.h>

void lean_initialize_runtime_module(void);

static int failures;

static void check_cascade_drop(char const * name, int before, int expected) {
    lean_object * child = lean_alloc_ctor(0, 0, 0);
    lean_internal_set_rc(child, before);

    lean_object * parent = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(parent, 0, child);
    lean_dec_ref(parent);

    int after = lean_internal_get_rc(child);
    if (after != expected) {
        fprintf(stderr, "%s: expected %d, got %d\n", name, expected, after);
        failures++;
    }

    lean_internal_set_rc(child, 1);
    lean_dec_ref(child);
}

int main(void) {
    lean_initialize_runtime_module();

    check_cascade_drop("sticky", LEAN_RC_STICKY, LEAN_RC_STICKY);
    check_cascade_drop("sticky-drop boundary", LEAN_RC_STICKY_DROP, LEAN_RC_STICKY_DROP);
    check_cascade_drop("live boundary", LEAN_RC_STICKY_DROP + 1, LEAN_RC_STICKY_DROP + 2);
    check_cascade_drop("persistent", 0, 0);

    return failures != 0;
}
