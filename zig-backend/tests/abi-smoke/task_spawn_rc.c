#include <assert.h>

#include <lean/lean.h>

extern void leanrt_test_allocator_reset_counters(void);
extern void leanrt_test_task_object_counter_reset(void);
extern size_t leanrt_test_task_object_alloc_count(void);
extern size_t leanrt_test_task_object_free_count(void);
extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);
extern _Bool leanrt_test_runtime_task_wait(lean_object * task);

static lean_object * return_one(lean_object * unit) {
    (void)unit;
    return lean_box(1);
}

int main(void) {
    assert(leanrt_test_runtime_task_manager_init(1));
    leanrt_test_allocator_reset_counters();
    leanrt_test_task_object_counter_reset();

    for (unsigned i = 0; i < 1000; ++i) {
        lean_object * closure = lean_alloc_closure((void *)return_one, 1, 0);
        lean_object * task = lean_task_spawn_core(closure, 0, 0);
        assert(leanrt_test_runtime_task_wait(task));
        lean_dec(task);
    }

    leanrt_test_runtime_task_manager_finalize();
    assert(leanrt_test_task_object_alloc_count() == leanrt_test_task_object_free_count());
    return 0;
}
