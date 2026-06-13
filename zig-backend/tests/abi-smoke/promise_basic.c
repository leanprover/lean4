#include <assert.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);

extern lean_object * lean_io_promise_new(void);

int main(void) {
    assert(leanrt_test_runtime_task_manager_init(1));

    lean_object * promise_obj = lean_io_promise_new();
    lean_promise_object * promise = lean_to_promise(promise_obj);
    lean_task_object * task = promise->m_result;

    assert(lean_obj_tag(promise_obj) == LeanPromise);
    assert(task != NULL);
    assert(lean_obj_tag((lean_object *)task) == LeanTask);
    assert(atomic_load_explicit(&task->m_value, memory_order_acquire) == NULL);
    assert(task->m_imp != NULL);
    assert(lean_io_get_task_state_core((lean_object *)task) != LEAN_TASK_STATE_FINISHED);

    lean_dec(promise_obj);
    leanrt_test_runtime_task_manager_finalize();
    return 0;
}
