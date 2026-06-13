#include <assert.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern lean_object * leanrt_test_alloc_task(lean_object * closure, unsigned prio, _Bool keep_alive);
extern void leanrt_test_free_task(lean_object * task);

static lean_object * return_forty_two(lean_object * unit) {
    (void)unit;
    return lean_box(42);
}

int main(void) {
    lean_object * closure = lean_alloc_closure((void *)return_forty_two, 1, 0);
    lean_object * task = leanrt_test_alloc_task(closure, 3, 0);
    lean_task_object * pending = lean_to_task(task);

    assert(lean_obj_tag(task) == LeanTask);
    assert(atomic_load_explicit(&pending->m_value, memory_order_acquire) == NULL);
    assert(pending->m_imp != NULL);
    assert(pending->m_imp->m_closure != NULL);
    assert(pending->m_imp->m_prio == 3);

    leanrt_test_free_task(task);
    return 0;
}
