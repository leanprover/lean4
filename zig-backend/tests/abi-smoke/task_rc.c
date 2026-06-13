#include <assert.h>
#include <stdlib.h>

#include <lean/lean.h>

extern lean_object * leanrt_test_alloc_task(lean_object * closure, unsigned prio, _Bool keep_alive);
extern void leanrt_test_free_task(lean_object * task);

static int abs_rc(const lean_object * obj) {
    return obj->m_rc < 0 ? -obj->m_rc : obj->m_rc;
}

static lean_object * return_five(lean_object * unit) {
    (void)unit;
    return lean_box(5);
}

static void test_spawn_consumes_owned_closure_and_returns_owned_task(void) {
    lean_object * closure = lean_alloc_closure((void *)return_five, 1, 0);
    lean_object * task = leanrt_test_alloc_task(closure, 0, 0);
    lean_task_object * spawned = lean_to_task(task);

    assert(abs_rc((lean_object *)spawned) == 1);
    leanrt_test_free_task(task);
}

static void test_shared_closure_drops_to_single_reference_after_spawn(void) {
    lean_object * closure = lean_alloc_closure((void *)return_five, 1, 0);
    lean_inc(closure);

    lean_object * task = leanrt_test_alloc_task(closure, 0, 0);

    assert(abs_rc((lean_object *)lean_to_task(task)) == 1);
    assert(abs_rc(closure) == 2);

    leanrt_test_free_task(task);
    lean_dec(closure);
}

int main(void) {
    test_spawn_consumes_owned_closure_and_returns_owned_task();
    test_shared_closure_drops_to_single_reference_after_spawn();
    return 0;
}
