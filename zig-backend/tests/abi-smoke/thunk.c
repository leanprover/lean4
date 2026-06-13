#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern void leanrt_test_reset_thunk_debug_counters(void);
extern size_t leanrt_test_get_thunk_st_path_count(void);
extern size_t leanrt_test_get_thunk_mt_path_count(void);
extern size_t leanrt_test_get_thunk_mt_cas_success_count(void);
extern size_t leanrt_test_get_thunk_mt_cas_fail_count(void);

static _Atomic int g_st_closure_calls = 0;
static _Atomic int g_mt_closure_calls = 0;
static _Atomic int g_mt_worker_ready = 0;
static _Atomic int g_mt_start_workers = 0;
static _Atomic int g_mt_closure_entered = 0;
static _Atomic int g_mt_release_result = 0;

static lean_object * st_thunk_closure(lean_object * w) {
    (void)w;
    atomic_fetch_add_explicit(&g_st_closure_calls, 1, memory_order_relaxed);
    return lean_box(123);
}

static lean_object * mt_thunk_closure(lean_object * w) {
    (void)w;
    atomic_fetch_add_explicit(&g_mt_closure_calls, 1, memory_order_relaxed);
    atomic_store_explicit(&g_mt_closure_entered, 1, memory_order_release);
    while (!atomic_load_explicit(&g_mt_release_result, memory_order_acquire)) {
        sched_yield();
    }
    return lean_box(77);
}

struct mt_thread_arg {
    lean_object * thunk;
    lean_object * result;
};

static void * mt_thunk_worker(void * raw) {
    struct mt_thread_arg * arg = (struct mt_thread_arg *)raw;
    atomic_fetch_add_explicit(&g_mt_worker_ready, 1, memory_order_acq_rel);
    while (!atomic_load_explicit(&g_mt_start_workers, memory_order_acquire)) {
        sched_yield();
    }
    arg->result = lean_thunk_get(arg->thunk);
    return NULL;
}

static lean_object * mk_thunk(lean_object * closure) {
    lean_thunk_object * thunk = (lean_thunk_object *)lean_alloc_object(sizeof(lean_thunk_object));
    lean_set_st_header((lean_object *)thunk, LeanThunk, 0);
    atomic_store_explicit(&thunk->m_value, NULL, memory_order_relaxed);
    atomic_store_explicit(&thunk->m_closure, closure, memory_order_relaxed);
    return (lean_object *)thunk;
}

static void test_st_path(void) {
    leanrt_test_reset_thunk_debug_counters();
    atomic_store_explicit(&g_st_closure_calls, 0, memory_order_release);

    lean_object * thunk = mk_thunk(lean_alloc_closure((void *)st_thunk_closure, 1, 0));
    lean_object * result = lean_thunk_get(thunk);

    assert(result == lean_box(123));
    assert(atomic_load_explicit(&g_st_closure_calls, memory_order_acquire) == 1);
    assert(leanrt_test_get_thunk_st_path_count() == 1);
    assert(leanrt_test_get_thunk_mt_path_count() == 0);
    assert(atomic_load_explicit(&lean_to_thunk(thunk)->m_closure, memory_order_acquire) == NULL);
    assert(atomic_load_explicit(&lean_to_thunk(thunk)->m_value, memory_order_acquire) == result);

    lean_dec(thunk);
}

static void test_mt_path(void) {
    leanrt_test_reset_thunk_debug_counters();
    atomic_store_explicit(&g_mt_closure_calls, 0, memory_order_release);
    atomic_store_explicit(&g_mt_worker_ready, 0, memory_order_release);
    atomic_store_explicit(&g_mt_start_workers, 0, memory_order_release);
    atomic_store_explicit(&g_mt_closure_entered, 0, memory_order_release);
    atomic_store_explicit(&g_mt_release_result, 0, memory_order_release);

    lean_object * thunk = mk_thunk(lean_alloc_closure((void *)mt_thunk_closure, 1, 0));
    lean_mark_mt(thunk);

    pthread_t threads[4];
    struct mt_thread_arg args[4] = {
        { .thunk = thunk, .result = NULL },
        { .thunk = thunk, .result = NULL },
        { .thunk = thunk, .result = NULL },
        { .thunk = thunk, .result = NULL },
    };

    for (size_t i = 0; i < 4; ++i) {
        assert(pthread_create(&threads[i], NULL, mt_thunk_worker, &args[i]) == 0);
    }

    while (atomic_load_explicit(&g_mt_worker_ready, memory_order_acquire) != 4) {
        sched_yield();
    }
    atomic_store_explicit(&g_mt_start_workers, 1, memory_order_release);

    while (!atomic_load_explicit(&g_mt_closure_entered, memory_order_acquire)) {
        sched_yield();
    }
    atomic_store_explicit(&g_mt_release_result, 1, memory_order_release);

    for (size_t i = 0; i < 4; ++i) {
        assert(pthread_join(threads[i], NULL) == 0);
        assert(args[i].result == lean_box(77));
    }

    assert(atomic_load_explicit(&g_mt_closure_calls, memory_order_acquire) == 1);
    assert(leanrt_test_get_thunk_st_path_count() == 0);
    assert(leanrt_test_get_thunk_mt_path_count() >= 1);
    assert(leanrt_test_get_thunk_mt_cas_success_count() == 1);
    assert(atomic_load_explicit(&lean_to_thunk(thunk)->m_closure, memory_order_acquire) == NULL);
    assert(atomic_load_explicit(&lean_to_thunk(thunk)->m_value, memory_order_acquire) == lean_box(77));

    (void)leanrt_test_get_thunk_mt_cas_fail_count();
    lean_dec(thunk);
}

int main(void) {
    test_st_path();
    test_mt_path();
    return 0;
}
