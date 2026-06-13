#include <assert.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_free_count(void);

static lean_object * mk_heap_object(void) {
    lean_object * obj = lean_alloc_object(sizeof(lean_object));
    lean_set_st_header(obj, 0, 0);
    return obj;
}

static void test_scalar_shape(void) {
    lean_object * task = lean_task_pure(lean_box(42));
    lean_task_object * pure = lean_to_task(task);

    assert(lean_obj_tag(task) == LeanTask);
    assert(atomic_load_explicit(&pure->m_value, memory_order_acquire) == lean_box(42));
    assert(pure->m_imp == NULL);
    assert(pure->m_header.m_rc == 1);

    lean_dec(task);
}

static void test_owned_value_released_with_task(void) {
    lean_object * task = lean_task_pure(mk_heap_object());

    leanrt_test_allocator_reset_counters();
    lean_dec(task);

    assert(leanrt_test_allocator_free_count() == 2);
}

int main(void) {
    test_scalar_shape();
    test_owned_value_released_with_task();
    return 0;
}
