/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include <vector>
#include <deque>
#include <cmath>
#include <lean/lean.h>
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/utf8.h"
#include "runtime/alloc.h"
#include "runtime/debug.h"
#include "runtime/hash.h"
#include "runtime/flet.h"
#include "runtime/interrupt.h"
#include "runtime/buffer.h"
#include "runtime/io.h"
#include "runtime/hash.h"

#if defined(__GLIBC__) || defined(__APPLE__)
    #define LEAN_SUPPORTS_BACKTRACE 1
#else
    #define LEAN_SUPPORTS_BACKTRACE 0
#endif

#if LEAN_SUPPORTS_BACKTRACE
#include <execinfo.h>
#include <unistd.h>
#endif

// HACK: for unknown reasons, std::isnan(x) fails on msys64 because math.h
// is imported and isnan(x) looks like a macro. On the other hand, isnan(x)
// fails on linux because <cmath> doesn't define it (as expected).
// So we declare isnan(x) as a macro for std::isnan(x) if it doesn't already exist.
#ifndef isnan
#define isnan(x) std::isnan(x)
#endif
#ifndef isfinite
#define isfinite(x) std::isfinite(x)
#endif
#ifndef isinf
#define isinf(x) std::isinf(x)
#endif

#if !defined(__STDC_VERSION_STDLIB_H__) || __STDC_VERSION_STDLIB_H__ < 202311L
extern "C" LEAN_EXPORT __attribute__((weak)) void free_sized(void *ptr, size_t) {
    free(ptr);
}
#endif

// see `Task.Priority.max`
#define LEAN_MAX_PRIO 8
#define LEAN_SYNC_PRIO std::numeric_limits<unsigned>::max()

namespace lean {

static bool should_abort_on_panic() {
#ifdef LEAN_EMSCRIPTEN
    return false;
#else
    return std::getenv("LEAN_ABORT_ON_PANIC");
#endif
}

static void abort_on_panic() {
    if (should_abort_on_panic()) {
        abort();
    }
}

extern "C" LEAN_EXPORT void lean_internal_panic(char const * msg) {
    std::cerr << "INTERNAL PANIC: " << msg << "\n";
    abort_on_panic();
    std::exit(1);
}

extern "C" LEAN_EXPORT void lean_internal_panic_out_of_memory() {
    lean_internal_panic("out of memory");
}

extern "C" LEAN_EXPORT void lean_internal_panic_unreachable() {
    lean_internal_panic("unreachable code has been reached");
}

extern "C" LEAN_EXPORT void lean_internal_panic_rc_overflow() {
    lean_internal_panic("reference counter overflowed");
}

bool g_exit_on_panic = false;
bool g_panic_messages = true;

extern "C" LEAN_EXPORT void lean_set_exit_on_panic(bool flag) {
    g_exit_on_panic = flag;
}

extern "C" LEAN_EXPORT void lean_set_panic_messages(bool flag) {
    g_panic_messages = flag;
}

static void panic_eprintln(char const * line, bool force_stderr) {
    if (force_stderr || g_exit_on_panic || should_abort_on_panic()) {
        // If we are about to kill the process, we should skip the Lean stderr buffer
        std::cerr << line << "\n";
    } else {
        io_eprintln(lean_mk_string(line));
    }
}

static void print_backtrace(bool force_stderr) {
#if LEAN_SUPPORTS_BACKTRACE
    void * bt_buf[100];
    int nptrs = backtrace(bt_buf, sizeof(bt_buf) / sizeof(void *));
    if (char ** symbols = backtrace_symbols(bt_buf, nptrs)) {
        for (int i = 0; i < nptrs; i++) {
            panic_eprintln(symbols[i], force_stderr);
        }
        // According to `man backtrace`, each `symbols[i]` should NOT be freed
        free(symbols);
        if (nptrs == sizeof(bt_buf)) {
            panic_eprintln("...", force_stderr);
        }
    }
#else
    panic_eprintln("(stack trace unavailable)", force_stderr);
#endif
}

extern "C" LEAN_EXPORT void lean_panic(char const * msg, bool force_stderr = false) {
    if (g_panic_messages) {
        panic_eprintln(msg, force_stderr);
#if LEAN_SUPPORTS_BACKTRACE
        char * bt_env = getenv("LEAN_BACKTRACE");
        if (!bt_env || strcmp(bt_env, "0") != 0) {
            panic_eprintln("backtrace:", force_stderr);
            print_backtrace(force_stderr);
        }
#endif
    }

    abort_on_panic();
    if (g_exit_on_panic) {
        std::exit(1);
    }
}

extern "C" LEAN_EXPORT object * lean_panic_fn(object * default_val, object * msg) {
    lean_panic(lean_string_cstr(msg));
    lean_dec(msg);
    return default_val;
}

extern "C" LEAN_EXPORT object * lean_sorry(uint8) {
    lean_internal_panic("executed 'sorry'");
    lean_unreachable();
}

extern "C" LEAN_EXPORT void lean_inc_ref_cold(lean_object * o) {
    std::atomic_fetch_sub_explicit(lean_get_rc_mt_addr(o), 1, std::memory_order_relaxed);
}

extern "C" LEAN_EXPORT void lean_inc_ref_n_cold(lean_object * o, unsigned n) {
    std::atomic_fetch_sub_explicit(lean_get_rc_mt_addr(o), (int)n, std::memory_order_relaxed);
}

extern "C" LEAN_EXPORT size_t lean_object_byte_size(lean_object * o) {
    if (o->m_cs_sz == 0) {
        /* Recall that multi-threaded, single-threaded and persistent objects are stored in the heap.
           Persistent objects are multi-threaded and/or single-threaded that have been "promoted" to
           a persistent status. */
        switch (lean_ptr_tag(o)) {
        case LeanArray:       return lean_array_byte_size(o);
        case LeanScalarArray: return lean_sarray_byte_size(o);
        case LeanString:      return lean_string_byte_size(o);
        default:              return lean_small_object_size(o);
        }
    } else {
        /* See comment at `lean_set_non_heap_header`, for small objects we store the object size in the RC field. */
        switch (lean_ptr_tag(o)) {
        case LeanArray:       return lean_array_byte_size(o);
        case LeanScalarArray: return lean_sarray_byte_size(o);
        case LeanString:      return lean_string_byte_size(o);
        default:              return o->m_cs_sz;
        }
    }
}

extern "C" LEAN_EXPORT size_t lean_object_data_byte_size(lean_object * o) {
    if (o->m_cs_sz == 0) {
        /* Recall that multi-threaded, single-threaded and persistent objects are stored in the heap.
           Persistent objects are multi-threaded and/or single-threaded that have been "promoted" to
           a persistent status. */
        switch (lean_ptr_tag(o)) {
        case LeanArray:       return lean_array_data_byte_size(o);
        case LeanScalarArray: return lean_sarray_data_byte_size(o);
        case LeanString:      return lean_string_data_byte_size(o);
        default:              return lean_small_object_size(o);
        }
    } else {
        /* See comment at `lean_set_non_heap_header`, for small objects we store the object size in the RC field. */
        switch (lean_ptr_tag(o)) {
        case LeanArray:       return lean_array_data_byte_size(o);
        case LeanScalarArray: return lean_sarray_data_byte_size(o);
        case LeanString:      return lean_string_data_byte_size(o);
        default:              return o->m_cs_sz;
        }
    }
}

static inline void lean_dealloc(lean_object * o, size_t sz) {
#ifdef LEAN_SMALL_ALLOCATOR
    dealloc(o, sz);
#else
    free_sized(o, sz);
#endif
}

extern "C" LEAN_EXPORT void lean_free_object(lean_object * o) {
    switch (lean_ptr_tag(o)) {
    case LeanArray:       return lean_dealloc(o, lean_array_byte_size(o));
    case LeanScalarArray: return lean_dealloc(o, lean_sarray_byte_size(o));
    case LeanString:      return lean_dealloc(o, lean_string_byte_size(o));
    case LeanMPZ:         to_mpz(o)->m_value.~mpz(); return lean_free_small_object(o);
    default:              return lean_free_small_object(o);
    }
}

static inline lean_object * get_next(lean_object * o) {
    if (sizeof(void*) == 8) {
        size_t header = ((size_t*)o)[0];
        LEAN_BYTE(header, 7) = 0;
        LEAN_BYTE(header, 6) = 0;
        return (lean_object*)(header);
    } else {
        // 32-bit version
        return ((lean_object**)o)[0];
    }
}

static inline void set_next(lean_object * o, lean_object * n) {
    if (sizeof(void*) == 8) {
        size_t new_header = (size_t)n;
        LEAN_BYTE(new_header, 7) = o->m_tag;
        LEAN_BYTE(new_header, 6) = o->m_other;
        ((size_t*)o)[0] = new_header;
        lean_assert(get_next(o) == n);
    } else {
        // 32-bit version
        ((lean_object**)o)[0] = n;
    }
}

static inline void push_back(lean_object * & todo, lean_object * v) {
    set_next(v, todo);
    todo = v;
}

static inline lean_object * pop_back(lean_object * & todo) {
    lean_object * r = todo;
    todo = get_next(todo);
    return r;
}

static inline void dec(lean_object * o, lean_object* & todo) {
    if (lean_is_scalar(o))
        return;
    if (LEAN_LIKELY(o->m_rc > 1)) {
        o->m_rc--;
    } else if (o->m_rc == 1) {
        push_back(todo, o);
    } else if (o->m_rc == 0) {
        return;
    } else if (std::atomic_fetch_add_explicit(lean_get_rc_mt_addr(o), 1, std::memory_order_acq_rel) == -1) {
        push_back(todo, o);
    }
}

#ifdef LEAN_LAZY_RC
LEAN_THREAD_PTR(object, g_to_free);
#endif

static void lean_del_core(object * o, object * & todo);

extern "C" LEAN_EXPORT lean_object * lean_alloc_object(size_t sz) {
#ifdef LEAN_LAZY_RC
     if (g_to_free) {
         object * o = pop_back(g_to_free);
         lean_del_core(o, g_to_free);
     }
#endif
#ifdef LEAN_SMALL_ALLOCATOR
    return (lean_object*)alloc(sz);
#else
    void * r = malloc(sz);
    if (r == nullptr) lean_internal_panic_out_of_memory();
    return (lean_object*)r;
#endif
}

static void deactivate_task(lean_task_object * t);
static void deactivate_promise(lean_promise_object * t);

static void lean_del_core(object * o, object * & todo) {
    uint8 tag = lean_ptr_tag(o);
    if (tag <= LeanMaxCtorTag) {
        object ** it  = lean_ctor_obj_cptr(o);
        object ** end = it + lean_ctor_num_objs(o);
        for (; it != end; ++it) dec(*it, todo);
        lean_free_small_object(o);
    } else {
        switch (tag) {
        case LeanClosure: {
            object ** it  = lean_closure_arg_cptr(o);
            object ** end = it + lean_closure_num_fixed(o);
            for (; it != end; ++it) dec(*it, todo);
            lean_free_small_object(o);
            break;
        }
        case LeanArray: {
            object ** it  = lean_array_cptr(o);
            object ** end = it + lean_array_size(o);
            for (; it != end; ++it) dec(*it, todo);
            lean_dealloc(o, lean_array_byte_size(o));
            break;
        }
        case LeanScalarArray:
            lean_dealloc(o, lean_sarray_byte_size(o));
            break;
        case LeanString:
            lean_dealloc(o, lean_string_byte_size(o));
            break;
        case LeanMPZ:
            to_mpz(o)->m_value.~mpz();
            lean_free_small_object(o);
            break;
        case LeanThunk:
            if (object * c = lean_to_thunk(o)->m_closure) dec(c, todo);
            if (object * v = lean_to_thunk(o)->m_value) dec(v, todo);
            lean_free_small_object(o);
            break;
        case LeanRef:
            if (object * v = lean_to_ref(o)->m_value) dec(v, todo);
            lean_free_small_object(o);
            break;
        case LeanTask:
            deactivate_task(lean_to_task(o));
            break;
        case LeanPromise:
            deactivate_promise(lean_to_promise(o));
            break;
        case LeanExternal:
            lean_to_external(o)->m_class->m_finalize(lean_to_external(o)->m_data);
            lean_free_small_object(o);
            break;
        default:
            lean_unreachable();
        }
    }
}

extern "C" LEAN_EXPORT void lean_dec_ref_cold(lean_object * o) {
    if (o->m_rc == 1 || std::atomic_fetch_add_explicit(lean_get_rc_mt_addr(o), 1, std::memory_order_acq_rel) == -1) {
#ifdef LEAN_LAZY_RC
        push_back(g_to_free, o);
#else
        object * todo = nullptr;
        while (true) {
            lean_del_core(o, todo);
            if (todo == nullptr)
                return;
            o = pop_back(todo);
        }
#endif
    }
}


// =======================================
// Closures

typedef object * (*lean_cfun2)(object *, object *); // NOLINT
typedef object * (*lean_cfun3)(object *, object *, object *); // NOLINT

static obj_res mk_closure_2_1(lean_cfun2 fn, obj_arg a) {
    object * c = lean_alloc_closure((void*)fn, 2, 1);
    lean_closure_set(c, 0, a);
    return c;
}

static obj_res mk_closure_3_2(lean_cfun3 fn, obj_arg a1, obj_arg a2) {
    object * c = lean_alloc_closure((void*)fn, 3, 2);
    lean_closure_set(c, 0, a1);
    lean_closure_set(c, 1, a2);
    return c;
}

// =======================================
// Arrays
static object * g_array_empty = nullptr;

object * array_mk_empty() {
    return g_array_empty;
}

extern "C" object * lean_list_to_array(object *, object *);
extern "C" object * lean_array_to_list_impl(object *, object *);

extern "C" LEAN_EXPORT object * lean_array_mk(lean_obj_arg lst) {
    return lean_list_to_array(lean_box(0), lst);
}

extern "C" LEAN_EXPORT lean_object * lean_array_to_list(lean_obj_arg a) {
    return lean_array_to_list_impl(lean_box(0), a);
}

extern "C" LEAN_EXPORT lean_obj_res lean_array_get_panic(lean_obj_arg def_val) {
    return lean_panic_fn(def_val, lean_mk_ascii_string_unchecked("Error: index out of bounds"));
}

extern "C" LEAN_EXPORT lean_obj_res lean_array_set_panic(lean_obj_arg a, lean_obj_arg v) {
    lean_dec(v);
    return lean_panic_fn(a, lean_mk_ascii_string_unchecked("Error: index out of bounds"));
}

// =======================================
// Thunks

extern "C" LEAN_EXPORT b_obj_res lean_thunk_get_core(b_obj_arg t) {
    object * c = lean_to_thunk(t)->m_closure.exchange(nullptr);
    if (c != nullptr) {
        /* Recall that a closure uses the standard calling convention.
           `thunk_get` "consumes" the result `r` by storing it at `to_thunk(t)->m_value`.
           Then, it returns a reference to this result to the caller.
           The behavior is compatible with `cnstr_obj` with also returns a reference
           to be object stored in the constructor object.

           Recall that `apply_1` also consumes `c`'s RC. */
        object * r = lean_apply_1(c, lean_box(0));
        lean_assert(r != nullptr); /* Closure must return a valid lean object */
        lean_assert(lean_to_thunk(t)->m_value == nullptr);
        mark_mt(r);
        lean_to_thunk(t)->m_value = r;
        return r;
    } else {
        lean_assert(c == nullptr);
        /* There is another thread executing the closure. We keep waiting for the m_value to be
           set by another thread. */
        while (!lean_to_thunk(t)->m_value) {
            this_thread::yield();
        }
        return lean_to_thunk(t)->m_value;
    }
}

// =======================================
// Mark Persistent

extern "C" void lean_mark_persistent(object * o);

static obj_res mark_persistent_fn(obj_arg o) {
    lean_mark_persistent(o);
    return lean_box(0);
}

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#include <sanitizer/lsan_interface.h>
#endif
#endif

extern "C" LEAN_EXPORT void lean_mark_persistent(object * o) {
    buffer<object*> todo;
    todo.push_back(o);
    while (!todo.empty()) {
        object * o = todo.back();
        todo.pop_back();
        if (!lean_is_scalar(o) && lean_has_rc(o)) {
            o->m_rc = 0;
#if defined(__has_feature)
#if __has_feature(address_sanitizer)
            // do not report as leak
            // NOTE: Most persistent objects are actually reachable from global
            // variables up to the end of the process. However, this is *not*
            // true for closures inside of persistent thunks, which are
            // "orphaned" after being evaluated.
            __lsan_ignore_object(o);
#endif
#endif
            uint8_t tag = lean_ptr_tag(o);
            if (tag <= LeanMaxCtorTag) {
                object ** it  = lean_ctor_obj_cptr(o);
                object ** end = it + lean_ctor_num_objs(o);
                for (; it != end; ++it) todo.push_back(*it);
            } else {
                switch (tag) {
                case LeanScalarArray:
                case LeanString:
                case LeanMPZ:
                    break;
                case LeanExternal: {
                    object * fn = lean_alloc_closure((void*)mark_persistent_fn, 1, 0);
                    lean_to_external(o)->m_class->m_foreach(lean_to_external(o)->m_data, fn);
                    lean_dec(fn);
                    break;
                }
                case LeanTask:
                    todo.push_back(lean_task_get(o));
                    break;
                case LeanPromise:
                    todo.push_back((lean_object *)lean_to_promise(o)->m_result);
                    break;
                case LeanClosure: {
                    object ** it  = lean_closure_arg_cptr(o);
                    object ** end = it + lean_closure_num_fixed(o);
                    for (; it != end; ++it) todo.push_back(*it);
                    break;
                }
                case LeanArray: {
                    object ** it  = lean_array_cptr(o);
                    object ** end = it + lean_array_size(o);
                    for (; it != end; ++it) todo.push_back(*it);
                    break;
                }
                case LeanThunk:
                    if (object * c = lean_to_thunk(o)->m_closure) todo.push_back(c);
                    if (object * v = lean_to_thunk(o)->m_value) todo.push_back(v);
                    break;
                case LeanRef:
                    if (object * v = lean_to_ref(o)->m_value) todo.push_back(v);
                    break;
                default:
                    lean_unreachable();
                    break;
                }
            }
        }
    }
}

// =======================================
// Mark MT

extern "C" void lean_mark_mt(object * o);

static obj_res mark_mt_fn(obj_arg o) {
    lean_mark_mt(o);
    lean_dec(o);
    return lean_box(0);
}

extern "C" LEAN_EXPORT void lean_mark_mt(object * o) {
#ifndef LEAN_MULTI_THREAD
    return;
#endif
    if (lean_is_scalar(o) || !lean_is_st(o)) return;

    buffer<object*> todo;
    todo.push_back(o);
    while (!todo.empty()) {
        object * o = todo.back();
        todo.pop_back();
        if (!lean_is_scalar(o) && lean_is_st(o)) {
            o->m_rc = -o->m_rc;
            uint8_t tag = lean_ptr_tag(o);
            if (tag <= LeanMaxCtorTag) {
                object ** it  = lean_ctor_obj_cptr(o);
                object ** end = it + lean_ctor_num_objs(o);
                for (; it != end; ++it) todo.push_back(*it);
            } else {
                switch (tag) {
                case LeanScalarArray:
                case LeanString:
                case LeanMPZ:
                    break;
                case LeanExternal: {
                    object * fn = lean_alloc_closure((void*)mark_mt_fn, 1, 0);
                    lean_to_external(o)->m_class->m_foreach(lean_to_external(o)->m_data, fn);
                    lean_dec(fn);
                    break;
                }
                case LeanTask:
                    todo.push_back(lean_task_get(o));
                    break;
                case LeanPromise:
                    todo.push_back((lean_object *)lean_to_promise(o)->m_result);
                    break;
                case LeanClosure: {
                    object ** it  = lean_closure_arg_cptr(o);
                    object ** end = it + lean_closure_num_fixed(o);
                    for (; it != end; ++it) todo.push_back(*it);
                    break;
                }
                case LeanArray: {
                    object ** it  = lean_array_cptr(o);
                    object ** end = it + lean_array_size(o);
                    for (; it != end; ++it) todo.push_back(*it);
                    break;
                }
                case LeanThunk:
                    if (object * c = lean_to_thunk(o)->m_closure) todo.push_back(c);
                    if (object * v = lean_to_thunk(o)->m_value) todo.push_back(v);
                    break;
                case LeanRef:
                    if (object * v = lean_to_ref(o)->m_value) todo.push_back(v);
                    break;
                default:
                    lean_unreachable();
                    break;
                }
            }
        }
    }
}

// =======================================
// Tasks

LEAN_THREAD_PTR(lean_task_object, g_current_task_object);

static lean_task_imp * alloc_task_imp(obj_arg c, unsigned prio, bool keep_alive) {
    lean_task_imp * imp = (lean_task_imp*)lean_alloc_small_object(sizeof(lean_task_imp));
    imp->m_closure     = c;
    imp->m_head_dep    = nullptr;
    imp->m_next_dep    = nullptr;
    imp->m_prio        = prio;
    imp->m_canceled    = false;
    imp->m_keep_alive  = keep_alive;
    imp->m_deleted     = false;
    return imp;
}

static void free_task_imp(lean_task_imp * imp) {
    lean_free_small_object((lean_object*)imp);
}

static void free_task(lean_task_object * t) {
    if (t->m_imp) free_task_imp(t->m_imp);
    lean_free_small_object((lean_object*)t);
}

struct scoped_current_task_object : flet<lean_task_object *> {
    scoped_current_task_object(lean_task_object * t):flet(g_current_task_object, t) {}
};

class task_manager {
    mutex                                         m_mutex;
    std::vector<std::unique_ptr<lthread>>         m_std_workers;
    unsigned                                      m_idle_std_workers{0};
    unsigned                                      m_max_std_workers{0};
    unsigned                                      m_num_dedicated_workers{0};
    std::deque<lean_task_object *>                m_queues[LEAN_MAX_PRIO+1];
    unsigned                                      m_queues_size{0};
    unsigned                                      m_max_prio{0};
    condition_variable                            m_queue_cv;
    condition_variable                            m_task_finished_cv;
    bool                                          m_shutting_down{false};

    lean_task_object * dequeue() {
        lean_assert(m_queues_size != 0);
        std::deque<lean_task_object *> & q = m_queues[m_max_prio];
        lean_assert(!q.empty());
        lean_task_object * result      = q.front();
        q.pop_front();
        m_queues_size--;
        if (q.empty()) {
            while (m_max_prio > 0) {
                --m_max_prio;
                if (!m_queues[m_max_prio].empty())
                    break;
            }
        }
        return result;
    }

    void enqueue_core(unique_lock<mutex> & lock, lean_task_object * t) {
        lean_assert(t->m_imp);
        unsigned prio = t->m_imp->m_prio;
        if (prio == LEAN_SYNC_PRIO) {
            run_task(lock, t);
            return;
        }
        if (prio > LEAN_MAX_PRIO) {
            spawn_dedicated_worker(t);
            return;
        }
        if (prio > m_max_prio)
            m_max_prio = prio;
        m_queues[prio].push_back(t);
        m_queues_size++;
        if (!m_idle_std_workers && m_std_workers.size() < m_max_std_workers)
            spawn_worker();
        else
            m_queue_cv.notify_one();
    }

    void deactivate_task_core(unique_lock<mutex> & lock, lean_task_object * t) {
        object * c              = t->m_imp->m_closure;
        lean_task_object * it   = t->m_imp->m_head_dep;
        t->m_imp->m_closure     = nullptr;
        t->m_imp->m_head_dep    = nullptr;
        t->m_imp->m_canceled    = true;
        t->m_imp->m_deleted     = true;
        lock.unlock();
        while (it) {
            lean_assert(it->m_imp->m_deleted);
            lean_task_object * next_it = it->m_imp->m_next_dep;
            free_task(it);
            it = next_it;
        }
        if (c) dec_ref(c);
        lock.lock();
    }

    void spawn_worker() {
        if (m_shutting_down)
            return;

        m_std_workers.emplace_back(new lthread([this]() {
            save_stack_info(false);
            unique_lock<mutex> lock(m_mutex);
            m_idle_std_workers++;
            while (true) {
                if (m_queues_size == 0 && m_shutting_down) {
                    break;
                }
                if (m_queues_size == 0 ||
                        // If we have reached the maximum number of standard workers (because the
                        // maximum was decreased by `task_get`), wait for someone else to become
                        // idle before picking up new work.
                        m_std_workers.size() - m_idle_std_workers >= m_max_std_workers) {
                    m_queue_cv.wait(lock);
                    continue;
                }

                lean_task_object * t = dequeue();
                m_idle_std_workers--;
                run_task(lock, t);
                m_idle_std_workers++;
                reset_heartbeat();
            }
            m_idle_std_workers--;
        }));
    }

    void spawn_dedicated_worker(lean_task_object * t) {
        m_num_dedicated_workers++;
        lthread([this, t]() {
            save_stack_info(false);
            unique_lock<mutex> lock(m_mutex);
            run_task(lock, t);
            m_num_dedicated_workers--;
        });
        // `lthread` will be implicitly freed, which frees up its control resources but does not terminate the thread
    }

    void run_task(unique_lock<mutex> & lock, lean_task_object * t) {
        lean_assert(t->m_imp);
        if (t->m_imp->m_deleted) {
            free_task(t);
            return;
        }
        reset_heartbeat();
        object * v = nullptr;
        {
            scoped_current_task_object scope_cur_task(t);
            object * c = t->m_imp->m_closure;
            t->m_imp->m_closure = nullptr;
            lock.unlock();
            v = lean_apply_1(c, box(0));
            // If deactivation was delayed by `m_keep_alive`, deactivate after the final execution (`v != nulltpr`)
            if (v != nullptr && t->m_imp->m_keep_alive) {
                lean_dec_ref((lean_object*)t);
            }
            lock.lock();
        }
        lean_assert(t->m_imp);
        if (t->m_imp->m_deleted) {
            lock.unlock();
            if (v) lean_dec(v);
            free_task(t);
            lock.lock();
        } else if (v != nullptr) {
            lean_assert(t->m_imp->m_closure == nullptr);
            resolve_core(lock, t, v);
        } else {
            // `bind` task has not finished yet, re-add as dependency of nested task
            // NOTE: closure MUST be extracted before unlocking the mutex as otherwise
            // another thread could deactivate the task and empty `m_clousure` in
            // between.
            object * c = t->m_imp->m_closure;
            lock.unlock();
            add_dep(lean_to_task(closure_arg_cptr(c)[0]), t);
            lock.lock();
        }
    }

    void resolve_core(unique_lock<mutex> & lock, lean_task_object * t, object * v) {
        mark_mt(v);
        t->m_value = v;
        lean_task_imp * imp = t->m_imp;
        t->m_imp   = nullptr;
        handle_finished(lock, t, imp);
        /* After the task has been finished and we propagated
           dependencies, we can release `imp` and keep just the value */
        free_task_imp(imp);
        m_task_finished_cv.notify_all();
    }

    void handle_finished(unique_lock<mutex> & lock, lean_task_object * t, lean_task_imp * imp) {
        lean_task_object * it = imp->m_head_dep;
        imp->m_head_dep = nullptr;
        while (it) {
            if (imp->m_canceled)
                it->m_imp->m_canceled = true;
            lean_task_object * next_it = it->m_imp->m_next_dep;
            it->m_imp->m_next_dep = nullptr;
            if (it->m_imp->m_deleted) {
                free_task(it);
            } else {
                enqueue_core(lock, it);
            }
            it = next_it;
        }
    }

    object * wait_any_check(object * task_list) {
        object * it = task_list;
        while (!is_scalar(it)) {
            object * head = lean_ctor_get(it, 0);
            if (lean_to_task(head)->m_value)
                return head;
            it = cnstr_get(it, 1);
        }
        return nullptr;
    }

public:
    task_manager(unsigned max_std_workers):
        m_max_std_workers(max_std_workers) {
    }

    ~task_manager() {
        {
            unique_lock<mutex> lock(m_mutex);
            m_shutting_down = true;
            // we can assume that `m_std_workers` will not be changed after this line
        }
        m_queue_cv.notify_all();
#ifndef LEAN_EMSCRIPTEN
        // wait for all workers to finish
        for (auto & t : m_std_workers)
            t->join();
        // never seems to terminate under Emscripten
#endif
    }

    void enqueue(lean_task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        enqueue_core(lock, t);
    }

    void resolve(lean_task_object * t, object * v) {
        if (t->m_value) {
            dec(v);
            return;
        }
        unique_lock<mutex> lock(m_mutex);
        if (t->m_value) {
            lock.unlock(); // `dec(v)` could lead to `deactivate_task` trying to take the lock
            dec(v);
            return;
        }
        resolve_core(lock, t, v);
    }

    void add_dep(lean_task_object * t1, lean_task_object * t2) {
        lean_assert(t2->m_value == nullptr);
        if (t1->m_value) {
            enqueue(t2);
            return;
        }
        unique_lock<mutex> lock(m_mutex);
        lean_assert(t2->m_value == nullptr);
        if (t1->m_value) {
            enqueue_core(lock, t2);
            return;
        }
        t2->m_imp->m_next_dep = t1->m_imp->m_head_dep;
        t1->m_imp->m_head_dep = t2;
    }

    void wait_for(lean_task_object * t) {
        if (t->m_value)
            return;
        unique_lock<mutex> lock(m_mutex);
        if (t->m_value)
            return;
        // see `Task.get`
        bool in_pool = g_current_task_object && g_current_task_object->m_imp->m_prio <= LEAN_MAX_PRIO;
        if (in_pool) {
            m_max_std_workers++;
            if (m_idle_std_workers == 0)
                spawn_worker();
            else
                m_queue_cv.notify_one();
        }
        m_task_finished_cv.wait(lock, [&]() { return t->m_value != nullptr; });
        if (in_pool) {
            m_max_std_workers--;
        }
    }

    object * wait_any(object * task_list) {
        if (object * t = wait_any_check(task_list))
            return t;
        unique_lock<mutex> lock(m_mutex);
        while (true) {
            if (object * t = wait_any_check(task_list))
                return t;
            m_task_finished_cv.wait(lock);
        }
    }

    void deactivate_task(lean_task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        if (object * v = t->m_value) {
            lean_assert(t->m_imp == nullptr);
            lock.unlock();
            lean_dec(v);
            free_task(t);
            return;
        } else {
            lean_assert(t->m_imp);
            deactivate_task_core(lock, t);
        }
    }

    void cancel(lean_task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        if (t->m_imp)
            t->m_imp->m_canceled = true;
    }

    bool shutting_down() const {
        return m_shutting_down;
    }
};

static task_manager * g_task_manager = nullptr;

extern "C" LEAN_EXPORT void lean_init_task_manager_using(unsigned num_workers) {
    lean_assert(g_task_manager == nullptr);
#if defined(LEAN_MULTI_THREAD)
    if (num_workers > 0) {
        g_task_manager = new task_manager(num_workers);
    }
#endif
}

static unsigned get_lean_num_threads() {
#ifndef LEAN_EMSCRIPTEN
    if (char const * num_threads = std::getenv("LEAN_NUM_THREADS")) {
        return atoi(num_threads);
    }
#endif
    return hardware_concurrency();
}

extern "C" LEAN_EXPORT void lean_init_task_manager() {
    lean_init_task_manager_using(get_lean_num_threads());
}

extern "C" LEAN_EXPORT void lean_finalize_task_manager() {
    if (g_task_manager) {
        delete g_task_manager;
        g_task_manager = nullptr;
    }
}

scoped_task_manager::scoped_task_manager(unsigned num_workers) {
    lean_assert(g_task_manager == nullptr);
#if defined(LEAN_MULTI_THREAD)
    if (num_workers > 0) {
        g_task_manager = new task_manager(num_workers);
    }
#endif
}

scoped_task_manager::~scoped_task_manager() {
    if (g_task_manager) {
        delete g_task_manager;
        g_task_manager = nullptr;
    }
}

void deactivate_task(lean_task_object * t) {
    if (g_task_manager) {
        g_task_manager->deactivate_task(t);
    } else {
        lean_assert(t->m_value != nullptr);
        lean_dec(t->m_value);
        free_task(t);
    }
}

static inline void lean_set_task_header(lean_object * o) {
    o->m_rc       = -1;
    o->m_tag      = LeanTask;
    o->m_other    = 0;
    o->m_cs_sz    = 0;
}

static lean_task_object * alloc_task(obj_arg c, unsigned prio, bool keep_alive) {
    lean_mark_mt(c);
    lean_task_object * o = (lean_task_object*)lean_alloc_small_object(sizeof(lean_task_object));
    lean_set_task_header((lean_object*)o);
    o->m_value = nullptr;
    o->m_imp   = alloc_task_imp(c, prio, keep_alive);
    if (keep_alive)
        lean_inc_ref((lean_object*)o);
    return o;
}

static lean_task_object * alloc_task(obj_arg v) {
    lean_task_object * o = (lean_task_object*)lean_alloc_small_object(sizeof(lean_task_object));
    lean_set_st_header((lean_object*)o, LeanTask, 0);
    o->m_value = v;
    o->m_imp   = nullptr;
    return o;
}


extern "C" LEAN_EXPORT obj_res lean_task_spawn_core(obj_arg c, unsigned prio, bool keep_alive) {
    if (!g_task_manager) {
        return lean_task_pure(apply_1(c, box(0)));
    } else {
        lean_task_object * new_task = alloc_task(c, prio, keep_alive);
        g_task_manager->enqueue(new_task);
        return (lean_object*)new_task;
    }
}

extern "C" LEAN_EXPORT obj_res lean_task_pure(obj_arg a) {
    return (lean_object*)alloc_task(a);
}

static obj_res task_map_fn(obj_arg f, obj_arg t, obj_arg) {
    b_obj_res v = lean_to_task(t)->m_value;
    lean_assert(v != nullptr);
    lean_inc(v);
    lean_dec_ref(t);
    return lean_apply_1(f, v);
}

extern "C" LEAN_EXPORT obj_res lean_task_map_core(obj_arg f, obj_arg t, unsigned prio,
      bool sync, bool keep_alive) {
    if (!g_task_manager || (sync && lean_to_task(t)->m_value)) {
        return lean_task_pure(apply_1(f, lean_task_get_own(t)));
    } else {
        lean_task_object * new_task = alloc_task(mk_closure_3_2(task_map_fn, f, t), sync ? LEAN_SYNC_PRIO : prio, keep_alive);
        g_task_manager->add_dep(lean_to_task(t), new_task);
        return (lean_object*)new_task;
    }
}

// We don't use `time_task` here as it's outside runtime/, and we wouldn't have access to `options`
// anyway
LEAN_EXPORT void (*g_lean_report_task_get_blocked_time)(std::chrono::nanoseconds) = nullptr;

extern "C" LEAN_EXPORT b_obj_res lean_task_get(b_obj_arg t) {
    if (object * v = lean_to_task(t)->m_value)
        return v;
    if (g_lean_report_task_get_blocked_time) {
        std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();
        g_task_manager->wait_for(lean_to_task(t));
        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        g_lean_report_task_get_blocked_time(std::chrono::nanoseconds(end - start));
    } else {
        g_task_manager->wait_for(lean_to_task(t));
    }
    lean_assert(lean_to_task(t)->m_value != nullptr);
    object * r = lean_to_task(t)->m_value;
    return r;
}

static obj_res task_bind_fn2(obj_arg t, obj_arg) {
    lean_assert(lean_to_task(t)->m_value);
    b_obj_res v = lean_to_task(t)->m_value;
    lean_inc(v);
    lean_dec_ref(t);
    return v;
}

static obj_res task_bind_fn1(obj_arg x, obj_arg f, obj_arg) {
    b_obj_res v = lean_to_task(x)->m_value;
    lean_assert(v != nullptr);
    lean_inc(v);
    lean_dec_ref(x);
    obj_res new_task = lean_apply_1(f, v);
    lean_assert(lean_is_task(new_task));
    lean_assert(g_current_task_object->m_imp);
    lean_assert(g_current_task_object->m_imp->m_closure == nullptr);
    obj_res c = mk_closure_2_1(task_bind_fn2, new_task);
    mark_mt(c);
    g_current_task_object->m_imp->m_closure = c;
    return nullptr; /* notify queue that task did not finish yet. */
}

extern "C" LEAN_EXPORT obj_res lean_task_bind_core(obj_arg x, obj_arg f, unsigned prio,
      bool sync, bool keep_alive) {
    if (!g_task_manager || (sync && lean_to_task(x)->m_value)) {
        return apply_1(f, lean_task_get_own(x));
    } else {
        lean_task_object * new_task = alloc_task(mk_closure_3_2(task_bind_fn1, x, f), sync ? LEAN_SYNC_PRIO : prio, keep_alive);
        g_task_manager->add_dep(lean_to_task(x), new_task);
        return (lean_object*)new_task;
    }
}

extern "C" LEAN_EXPORT bool lean_io_check_canceled_core() {
    if (lean_task_object * t = g_current_task_object) {
        lean_assert(t->m_imp); // task is being executed
        return t->m_imp->m_canceled || g_task_manager->shutting_down();
    }
    return false;
}

extern "C" LEAN_EXPORT void lean_io_cancel_core(b_obj_arg t) {
    if (lean_to_task(t)->m_value)
        return;
    g_task_manager->cancel(lean_to_task(t));
}

extern "C" LEAN_EXPORT uint8_t lean_io_get_task_state_core(b_obj_arg t) {
    lean_task_object * o = lean_to_task(t);
    if (o->m_imp) {
        if (o->m_imp->m_closure) {
            return 0; // waiting (waiting/queued)
        } else {
            return 1; // running (running/promised)
        }
    } else {
        return 2; // finished
    }
}

extern "C" LEAN_EXPORT b_obj_res lean_io_wait_any_core(b_obj_arg task_list) {
    return g_task_manager->wait_any(task_list);
}

extern "C" LEAN_EXPORT obj_res lean_io_promise_new(obj_arg) {
    lean_always_assert(g_task_manager);

    bool keep_alive = false;
    unsigned prio = 0;
    object * closure = nullptr;
    lean_task_object * t = (lean_task_object*)lean_alloc_small_object(sizeof(lean_task_object));
    lean_set_task_header((lean_object*)t);
    t->m_value = nullptr;
    t->m_imp   = alloc_task_imp(closure, prio, keep_alive);

    lean_promise_object * o = (lean_promise_object *)lean_alloc_small_object(sizeof(lean_promise_object));
    lean_set_st_header((lean_object *)o, LeanPromise, 0);
    o->m_result = t; // the promise takes ownership of one task token

    return io_result_mk_ok((lean_object *) o);
}

extern "C" LEAN_EXPORT obj_res lean_io_promise_resolve(obj_arg value, b_obj_arg promise, obj_arg) {
    g_task_manager->resolve(lean_to_promise(promise)->m_result, mk_option_some(value));
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_promise_result_opt(b_obj_arg promise) {
    lean_object * t = (lean_object *)lean_to_promise(promise)->m_result;
    lean_inc_ref(t);
    return t;
}

void deactivate_promise(lean_promise_object * promise) {
    g_task_manager->resolve(promise->m_result, mk_option_none());
    lean_dec_ref((lean_object *)promise->m_result);
    lean_free_small_object((lean_object *)promise);
}

// =======================================
// Natural numbers

object * alloc_mpz(mpz const & m) {
    void * mem = lean_alloc_small_object(sizeof(mpz_object));
    mpz_object * o = new (mem) mpz_object(m);
    lean_set_st_header((lean_object*)o, LeanMPZ, 0);
    return (lean_object*)o;
}

#ifdef LEAN_USE_GMP
extern "C" LEAN_EXPORT lean_object * lean_alloc_mpz(mpz_t v) {
    return alloc_mpz(mpz(v));
}

extern "C" LEAN_EXPORT void lean_extract_mpz_value(lean_object * o, mpz_t v) {
    return to_mpz(o)->m_value.set(v);
}
#endif

object * mpz_to_nat_core(mpz const & m) {
    lean_assert(!m.is_size_t() || m.get_size_t() > LEAN_MAX_SMALL_NAT);
    return alloc_mpz(m);
}

static inline obj_res mpz_to_nat(mpz const & m) {
    if (m.is_size_t() && m.get_size_t() <= LEAN_MAX_SMALL_NAT)
        return lean_box(m.get_size_t());
    else
        return mpz_to_nat_core(m);
}

extern "C" LEAN_EXPORT object * lean_cstr_to_nat(char const * n) {
    return mpz_to_nat(mpz(n));
}

extern "C" LEAN_EXPORT object * lean_big_usize_to_nat(size_t n) {
    if (n <= LEAN_MAX_SMALL_NAT) {
        return lean_box(n);
    } else {
        return mpz_to_nat_core(mpz::of_size_t(n));
    }
}

extern "C" LEAN_EXPORT object * lean_big_uint64_to_nat(uint64_t n) {
    if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT)) {
        return lean_box(n);
    } else {
        return mpz_to_nat_core(mpz(n));
    }
}

extern "C" LEAN_EXPORT object * lean_nat_big_succ(object * a) {
    return mpz_to_nat_core(mpz_value(a) + 1);
}

extern "C" LEAN_EXPORT object * lean_nat_big_add(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat_core(mpz::of_size_t(lean_unbox(a1)) + mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat_core(mpz_value(a1) + mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat_core(mpz_value(a1) + mpz_value(a2));
}

extern "C" LEAN_EXPORT object * lean_nat_big_sub(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1)) {
        lean_assert(mpz::of_size_t(lean_unbox(a1)) < mpz_value(a2));
        return lean_box(0);
    } else if (lean_is_scalar(a2)) {
        lean_assert(mpz_value(a1) > mpz::of_size_t(lean_unbox(a2)));
        return mpz_to_nat(mpz_value(a1) - mpz::of_size_t(lean_unbox(a2)));
    } else {
        if (mpz_value(a1) < mpz_value(a2))
            return lean_box(0);
        else
            return mpz_to_nat(mpz_value(a1) - mpz_value(a2));
    }
}

extern "C" LEAN_EXPORT object * lean_nat_big_mul(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) * mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat(mpz_value(a1) * mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat_core(mpz_value(a1) * mpz_value(a2));
}

extern "C" LEAN_EXPORT object * lean_nat_overflow_mul(size_t a1, size_t a2) {
    return mpz_to_nat(mpz::of_size_t(a1) * mpz::of_size_t(a2));
}

extern "C" LEAN_EXPORT object * lean_nat_big_div(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        lean_assert(mpz::of_size_t(lean_unbox(a1)) / mpz_value(a2) == 0);
        return lean_box(0);
    } else if (lean_is_scalar(a2)) {
        usize n2 = lean_unbox(a2);
        return n2 == 0 ? a2 : mpz_to_nat(mpz_value(a1) / mpz::of_size_t(n2));
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mpz_to_nat(mpz_value(a1) / mpz_value(a2));
    }
}

extern "C" LEAN_EXPORT object * lean_nat_big_mod(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        return a1;
    } else if (lean_is_scalar(a2)) {
        usize n2 = lean_unbox(a2);
        if (n2 == 0) {
            lean_inc(a1);
            return a1;
        } else {
            return mpz_to_nat(mpz_value(a1) % mpz::of_size_t(n2));
        }
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mpz_to_nat(mpz_value(a1) % mpz_value(a2));
    }
}

extern "C" LEAN_EXPORT bool lean_nat_big_eq(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        lean_assert(mpz::of_size_t(lean_unbox(a1)) != mpz_value(a2));
        return false;
    } else if (lean_is_scalar(a2)) {
        lean_assert(mpz_value(a1) != mpz::of_size_t(lean_unbox(a2)));
        return false;
    } else {
        return mpz_value(a1) == mpz_value(a2);
    }
}

extern "C" LEAN_EXPORT bool lean_nat_big_le(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        lean_assert(mpz::of_size_t(lean_unbox(a1)) < mpz_value(a2))
        return true;
    } else if (lean_is_scalar(a2)) {
        lean_assert(mpz_value(a1) > mpz::of_size_t(lean_unbox(a2)));
        return false;
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

extern "C" LEAN_EXPORT bool lean_nat_big_lt(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        lean_assert(mpz::of_size_t(lean_unbox(a1)) < mpz_value(a2));
        return true;
    } else if (lean_is_scalar(a2)) {
        lean_assert(mpz_value(a1) > mpz::of_size_t(lean_unbox(a2)));
        return false;
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

extern "C" LEAN_EXPORT object * lean_nat_big_land(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) & mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat(mpz_value(a1) & mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat(mpz_value(a1) & mpz_value(a2));
}

extern "C" LEAN_EXPORT object * lean_nat_big_lor(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) | mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat(mpz_value(a1) | mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat(mpz_value(a1) | mpz_value(a2));
}

extern "C" LEAN_EXPORT object * lean_nat_big_xor(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) ^ mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat(mpz_value(a1) ^ mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat(mpz_value(a1) ^ mpz_value(a2));
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_shiftl(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    // Special case for shifted value is 0.
    if (lean_is_scalar(a1) && lean_unbox(a1) == 0) {
        return lean_box(0);
    }
    auto a = lean_is_scalar(a1)
           ? mpz::of_size_t(lean_unbox(a1))
           : mpz_value(a1);
    if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
        lean_internal_panic("Nat.shiftl exponent is too big");
    }
    mpz r;
    mul2k(r, a, lean_unbox(a2));
    return mpz_to_nat(r);
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_shiftr(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (!lean_is_scalar(a2)) {
        return lean_box(0); // This large of an exponent must be 0.
    }
    auto a = lean_is_scalar(a1)
           ? mpz::of_size_t(lean_unbox(a1))
           : mpz_value(a1);
    size_t s = lean_unbox(a2);
    // If the shift amount is large, then we fail if it is not large
    // enough to zero out all the bits.
    if (s > UINT_MAX) {
        if (a.log2() >= s) {
            lean_internal_panic("Nat.shiftr exponent is too big");
        } else {
            return lean_box(0);
        }
    }
    mpz r;
    div2k(r, a, s);
    return mpz_to_nat(r);
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_pow(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
        lean_internal_panic("Nat.pow exponent is too big");
    }
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)).pow(lean_unbox(a2)));
    else
        return mpz_to_nat(mpz_value(a1).pow(lean_unbox(a2)));
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_gcd(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (lean_is_scalar(a1)) {
      if (lean_is_scalar(a2))
        return mpz_to_nat(gcd(mpz::of_size_t(lean_unbox(a1)), mpz::of_size_t(lean_unbox(a2))));
      else
        return mpz_to_nat(gcd(mpz::of_size_t(lean_unbox(a1)), mpz_value(a2)));
    } else {
      if (lean_is_scalar(a2))
        return mpz_to_nat(gcd(mpz_value(a1), mpz::of_size_t(lean_unbox(a2))));
      else
        return mpz_to_nat(gcd(mpz_value(a1), mpz_value(a2)));
    }
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_log2(b_lean_obj_arg a) {
    if (lean_is_scalar(a)) {
      unsigned res = 0;
      size_t n = lean_unbox(a);
      while (n >= 2) {
        res++;
        n /= 2;
      }
      return lean_box(res);
    } else {
      return lean_box(mpz_value(a).log2());
    }
}

// =======================================
// Integers

inline object * mpz_to_int_core(mpz const & m) {
    lean_assert(m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT);
    return alloc_mpz(m);
}

static object * mpz_to_int(mpz const & m) {
    if (m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT)
        return mpz_to_int_core(m);
    else
        return lean_box(static_cast<unsigned>(m.get_int()));
}

extern "C" LEAN_EXPORT lean_obj_res lean_big_int_to_nat(lean_obj_arg a) {
    lean_assert(!lean_is_scalar(a));
    mpz m = mpz_value(a);
    lean_dec(a);
    return mpz_to_nat(m);
}

extern "C" LEAN_EXPORT object * lean_cstr_to_int(char const * n) {
    return mpz_to_int(mpz(n));
}

extern "C" LEAN_EXPORT object * lean_big_int_to_int(int n) {
    return alloc_mpz(mpz(n));
}

extern "C" LEAN_EXPORT object * lean_big_size_t_to_int(size_t n) {
    return alloc_mpz(mpz::of_size_t(n));
}

extern "C" LEAN_EXPORT object * lean_big_int64_to_int(int64_t n) {
    if (LEAN_LIKELY(LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT)) {
        return lean_box(static_cast<unsigned>(static_cast<int>(n)));
    } else {
        return mpz_to_int_core(mpz(n));
    }
}

extern "C" LEAN_EXPORT object * lean_int_big_neg(object * a) {
    return mpz_to_int(neg(mpz_value(a)));
}

extern "C" LEAN_EXPORT object * lean_int_big_add(object * a1, object * a2) {
    if (lean_is_scalar(a1))
        return mpz_to_int(lean_scalar_to_int(a1) + mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_int(mpz_value(a1) + lean_scalar_to_int(a2));
    else
        return mpz_to_int(mpz_value(a1) + mpz_value(a2));
}

extern "C" LEAN_EXPORT object * lean_int_big_sub(object * a1, object * a2) {
    if (lean_is_scalar(a1))
        return mpz_to_int(lean_scalar_to_int(a1) - mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_int(mpz_value(a1) - lean_scalar_to_int(a2));
    else
        return mpz_to_int(mpz_value(a1) - mpz_value(a2));
}

extern "C" LEAN_EXPORT object * lean_int_big_mul(object * a1, object * a2) {
    if (lean_is_scalar(a1))
        return mpz_to_int(lean_scalar_to_int(a1) * mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_int(mpz_value(a1) * lean_scalar_to_int(a2));
    else
        return mpz_to_int(mpz_value(a1) * mpz_value(a2));
}

extern "C" LEAN_EXPORT object * lean_int_big_div(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        return mpz_to_int(lean_scalar_to_int(a1) / mpz_value(a2));
    } else if (lean_is_scalar(a2)) {
        int d = lean_scalar_to_int(a2);
        if (d == 0)
            return a2;
        else
            return mpz_to_int(mpz_value(a1) / d);
    } else {
        return mpz_to_int(mpz_value(a1) / mpz_value(a2));
    }
}

extern "C" LEAN_EXPORT object * lean_int_big_mod(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        return mpz_to_int(mpz(lean_scalar_to_int(a1)) % mpz_value(a2));
    } else if (lean_is_scalar(a2)) {
        int i2 = lean_scalar_to_int(a2);
        if (i2 == 0) {
            lean_inc(a1);
            return a1;
        } else {
            return mpz_to_int(mpz_value(a1) % mpz(i2));
        }
    } else {
        return mpz_to_int(mpz_value(a1) % mpz_value(a2));
    }
}

extern "C" LEAN_EXPORT object * lean_int_big_ediv(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        return mpz_to_int(mpz::ediv(lean_scalar_to_int(a1), mpz_value(a2)));
    } else if (lean_is_scalar(a2)) {
        int d = lean_scalar_to_int(a2);
        if (d == 0)
            return a2;
        else
            return mpz_to_int(mpz::ediv(mpz_value(a1), d));
    } else {
        return mpz_to_int(mpz::ediv(mpz_value(a1), mpz_value(a2)));
    }
}

extern "C" LEAN_EXPORT object * lean_int_big_emod(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        return mpz_to_int(mpz::emod(lean_scalar_to_int(a1), mpz_value(a2)));
    } else if (lean_is_scalar(a2)) {
        int i2 = lean_scalar_to_int(a2);
        if (i2 == 0) {
            lean_inc(a1);
            return a1;
        } else {
            return mpz_to_int(mpz::emod(mpz_value(a1), i2));
        }
    } else {
        return mpz_to_int(mpz::emod(mpz_value(a1), mpz_value(a2)));
    }
}

extern "C" LEAN_EXPORT bool lean_int_big_eq(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        lean_assert(lean_scalar_to_int(a1) != mpz_value(a2))
        return false;
    } else if (lean_is_scalar(a2)) {
        lean_assert(mpz_value(a1) != lean_scalar_to_int(a2))
        return false;
    } else {
        return mpz_value(a1) == mpz_value(a2);
    }
}

extern "C" LEAN_EXPORT bool lean_int_big_le(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        return lean_scalar_to_int(a1) <= mpz_value(a2);
    } else if (lean_is_scalar(a2)) {
        return mpz_value(a1) <= lean_scalar_to_int(a2);
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

extern "C" LEAN_EXPORT bool lean_int_big_lt(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        return lean_scalar_to_int(a1) < mpz_value(a2);
    } else if (lean_is_scalar(a2)) {
        return mpz_value(a1) < lean_scalar_to_int(a2);
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

extern "C" LEAN_EXPORT bool lean_int_big_nonneg(object * a) {
    return mpz_value(a) >= 0;
}

// =======================================
// UInt

extern "C" LEAN_EXPORT uint8 lean_uint8_of_big_nat(b_obj_arg a) {
    return mpz_value(a).mod8();
}

extern "C" LEAN_EXPORT uint16 lean_uint16_of_big_nat(b_obj_arg a) {
    return mpz_value(a).mod16();
}

extern "C" LEAN_EXPORT uint32 lean_uint32_of_big_nat(b_obj_arg a) {
    return mpz_value(a).mod32();
}

extern "C" LEAN_EXPORT uint64 lean_uint64_of_big_nat(b_obj_arg a) {
    return mpz_value(a).mod64();
}

extern "C" LEAN_EXPORT uint64 lean_uint64_mix_hash(uint64 a1, uint64 a2) {
  return hash(a1, a2);
}

extern "C" LEAN_EXPORT usize lean_usize_of_big_nat(b_obj_arg a) {
    return mpz_value(a).get_size_t();
}

// =======================================
// IntX

extern "C" LEAN_EXPORT int8 lean_int8_of_big_int(b_obj_arg a) {
    return mpz_value(a).smod8();
}

extern "C" LEAN_EXPORT int16 lean_int16_of_big_int(b_obj_arg a) {
    return mpz_value(a).smod16();
}

extern "C" LEAN_EXPORT int32 lean_int32_of_big_int(b_obj_arg a) {
    return mpz_value(a).smod32();
}

extern "C" LEAN_EXPORT int64 lean_int64_of_big_int(b_obj_arg a) {
    return mpz_value(a).smod64();
}

extern "C" LEAN_EXPORT isize lean_isize_of_big_int(b_obj_arg a) {
    if (sizeof(ptrdiff_t) == 8) {
        return static_cast<isize>(mpz_value(a).smod64());
    } else {
        // We assert in int.h that the size of ptrdiff_t is 8 or 4.
        return static_cast<isize>(mpz_value(a).smod32());
    }
}

// =======================================
// Float

extern "C" LEAN_EXPORT lean_obj_res lean_float_to_string(double a) {
    if (isnan(a))
        // override NaN because we don't want NaNs to be distinguishable
        // because the sign bit / payload bits can be architecture-dependent
        return mk_ascii_string_unchecked("NaN");
    else
        return mk_ascii_string_unchecked(std::to_string(a));
}

extern "C" LEAN_EXPORT double lean_float_scaleb(double a, b_lean_obj_arg b) {
   if (lean_is_scalar(b)) {
     return scalbn(a, lean_scalar_to_int(b));
   } else if (a == 0 || mpz_value(b).is_neg()) {
     return 0;
   } else {
     return a * (1.0 / 0.0);
   }
}

extern "C" LEAN_EXPORT uint8_t lean_float_isnan(double a) { return (bool) isnan(a); }
extern "C" LEAN_EXPORT uint8_t lean_float_isfinite(double a) { return (bool) isfinite(a); }
extern "C" LEAN_EXPORT uint8_t lean_float_isinf(double a) { return (bool) isinf(a); }
extern "C" LEAN_EXPORT obj_res lean_float_frexp(double a) {
    object* r = lean_alloc_ctor(0, 2, 0);
    int exp;
    lean_ctor_set(r, 0, lean_box_float(frexp(a, &exp)));
    lean_ctor_set(r, 1, isfinite(a) ? lean_int_to_int(exp) : lean_box(0));
    return r;
}

extern "C" LEAN_EXPORT double lean_float_of_bits(uint64_t u)
{
    static_assert(sizeof(double) == sizeof(u), "`double` unexpected size.");
    double ret;
    std::memcpy(&ret, &u, sizeof(double));
    if (isnan(ret))
        ret = std::numeric_limits<double>::quiet_NaN();
    return ret;
}

extern "C" LEAN_EXPORT uint64_t lean_float_to_bits(double d)
{
    uint64_t ret;
    if (isnan(d))
        d = std::numeric_limits<double>::quiet_NaN();
    std::memcpy(&ret, &d, sizeof(double));
    return ret;
}

// =======================================
// Float32

extern "C" LEAN_EXPORT lean_obj_res lean_float32_to_string(float a) {
    if (isnan(a))
        // override NaN because we don't want NaNs to be distinguishable
        // because the sign bit / payload bits can be architecture-dependent
        return mk_ascii_string_unchecked("NaN");
    else
        return mk_ascii_string_unchecked(std::to_string(a));
}

extern "C" LEAN_EXPORT float lean_float32_scaleb(float a, b_lean_obj_arg b) {
   if (lean_is_scalar(b)) {
     return scalbn(a, lean_scalar_to_int(b));
   } else if (a == 0 || mpz_value(b).is_neg()) {
     return 0;
   } else {
     return a * (1.0 / 0.0);
   }
}

extern "C" LEAN_EXPORT uint8_t lean_float32_isnan(float a) { return (bool) isnan(a); }
extern "C" LEAN_EXPORT uint8_t lean_float32_isfinite(float a) { return (bool) isfinite(a); }
extern "C" LEAN_EXPORT uint8_t lean_float32_isinf(float a) { return (bool) isinf(a); }
extern "C" LEAN_EXPORT obj_res lean_float32_frexp(float a) {
    object* r = lean_alloc_ctor(0, 2, 0);
    int exp;
    lean_ctor_set(r, 0, lean_box_float32(frexp(a, &exp)));
    lean_ctor_set(r, 1, isfinite(a) ? lean_int_to_int(exp) : lean_box(0));
    return r;
}

extern "C" LEAN_EXPORT float lean_float32_of_bits(uint32_t u)
{
    static_assert(sizeof(float) == sizeof(u), "`float` unexpected size.");
    float ret;
    std::memcpy(&ret, &u, sizeof(float));
    if (isnan(ret))
        ret = std::numeric_limits<float>::quiet_NaN();
    return ret;
}

extern "C" LEAN_EXPORT uint32_t lean_float32_to_bits(float d)
{
    uint32_t ret;
    if (isnan(d))
        d = std::numeric_limits<float>::quiet_NaN();
    std::memcpy(&ret, &d, sizeof(float));
    return ret;
}

// =======================================
// Strings

static inline char * w_string_cstr(object * o) { lean_assert(lean_is_string(o)); return lean_to_string(o)->m_data; }

static object * string_ensure_capacity(object * o, size_t extra) {
    lean_assert(is_exclusive(o));
    size_t sz  = string_size(o);
    size_t cap = string_capacity(o);
    if (sz + extra > cap) {
        object * new_o = alloc_string(sz, cap + sz + extra, string_len(o));
        lean_assert(string_capacity(new_o) >= sz + extra);
        memcpy(w_string_cstr(new_o), string_cstr(o), sz);
        lean_dealloc(o, lean_string_byte_size(o));
        return new_o;
    } else {
        return o;
    }
}

extern "C" LEAN_EXPORT object * lean_mk_string_unchecked(char const * s, size_t sz, size_t len) {
    size_t rsz = sz + 1;
    object * r = lean_alloc_string(rsz, rsz, len);
    memcpy(w_string_cstr(r), s, sz);
    w_string_cstr(r)[sz] = 0;
    return r;
}

object * lean_mk_string_lossy_recover(char const * s, size_t sz, size_t pos, size_t i) {
    std::string str(s, pos);
    size_t start = pos;
    while (pos < sz) {
        if (!validate_utf8_one((const uint8_t *)s, sz, pos)) {
            str.append(s + start, pos - start);
            str.append("\ufffd"); // U+FFFD REPLACEMENT CHARACTER
            do pos++; while (pos < sz && (s[pos] & 0xc0) == 0x80);
            start = pos;
        }
        i++;
    }
    str.append(s + start, pos - start);
    return lean_mk_string_unchecked(str.data(), str.size(), i);
}

extern "C" LEAN_EXPORT object * lean_mk_string_from_bytes(char const * s, size_t sz) {
    size_t pos = 0, i = 0;
    if (validate_utf8((const uint8_t *)s, sz, pos, i)) {
        return lean_mk_string_unchecked(s, pos, i);
    } else {
        return lean_mk_string_lossy_recover(s, sz, pos, i);
    }
}

extern "C" LEAN_EXPORT object * lean_mk_string_from_bytes_unchecked(char const * s, size_t sz) {
    return lean_mk_string_unchecked(s, sz, utf8_strlen(s, sz));
}

extern "C" LEAN_EXPORT object * lean_mk_string(char const * s) {
    return lean_mk_string_from_bytes(s, strlen(s));
}

extern "C" LEAN_EXPORT object * lean_mk_ascii_string_unchecked(char const * s) {
    size_t len = strlen(s);
    return lean_mk_string_unchecked(s, len, len);
}

extern "C" LEAN_EXPORT obj_res lean_string_from_utf8_unchecked(b_obj_arg a) {
    return lean_mk_string_from_bytes_unchecked(reinterpret_cast<char *>(lean_sarray_cptr(a)), lean_sarray_size(a));
}

extern "C" LEAN_EXPORT uint8 lean_string_validate_utf8(b_obj_arg a) {
    size_t pos = 0, i = 0;
    return validate_utf8(lean_sarray_cptr(a), lean_sarray_size(a), pos, i);
}

extern "C" LEAN_EXPORT obj_res lean_string_to_utf8(b_obj_arg s) {
    size_t sz = lean_string_size(s) - 1;
    obj_res r = lean_alloc_sarray(1, sz, sz);
    memcpy(lean_sarray_cptr(r), lean_string_cstr(s), sz);
    return r;
}

object * mk_string(std::string const & s) {
    return lean_mk_string_from_bytes(s.data(), s.size());
}

object * mk_ascii_string_unchecked(std::string const & s) {
    return lean_mk_string_unchecked(s.data(), s.size(), s.size());
}

std::string string_to_std(b_obj_arg o) {
    lean_assert(string_size(o) > 0);
    return std::string(w_string_cstr(o), lean_string_size(o) - 1);
}

static size_t mk_capacity(size_t sz) {
    return sz*2;
}

extern "C" LEAN_EXPORT object * lean_string_push(object * s, unsigned c) {
    size_t sz  = lean_string_size(s);
    size_t len = lean_string_len(s);
    object * r;
    if (!lean_is_exclusive(s)) {
        r = lean_alloc_string(sz, mk_capacity(sz+5), len);
        memcpy(w_string_cstr(r), lean_string_cstr(s), sz - 1);
        lean_dec_ref(s);
    } else {
        r = string_ensure_capacity(s, 5);
    }
    unsigned consumed = push_unicode_scalar(w_string_cstr(r) + sz - 1, c);
    lean_to_string(r)->m_size   = sz + consumed;
    lean_to_string(r)->m_length++;
    w_string_cstr(r)[sz + consumed - 1] = 0;
    return r;
}

extern "C" LEAN_EXPORT object * lean_string_append(object * s1, object * s2) {
    size_t sz1      = lean_string_size(s1);
    size_t sz2      = lean_string_size(s2);
    size_t len1     = lean_string_len(s1);
    size_t len2     = lean_string_len(s2);
    size_t new_len  = len1 + len2;
    size_t new_sz   = sz1 + sz2 - 1;
    object * r;
    if (!lean_is_exclusive(s1)) {
        r = lean_alloc_string(new_sz, mk_capacity(new_sz), new_len);
        memcpy(w_string_cstr(r), lean_string_cstr(s1), sz1 - 1);
        dec_ref(s1);
    } else {
        lean_assert(s1 != s2);
        r = string_ensure_capacity(s1, sz2-1);
    }
    memcpy(w_string_cstr(r) + sz1 - 1, lean_string_cstr(s2), sz2 - 1);
    lean_to_string(r)->m_size   = new_sz;
    lean_to_string(r)->m_length = new_len;
    w_string_cstr(r)[new_sz - 1] = 0;
    return r;
}

extern "C" LEAN_EXPORT bool lean_string_eq_cold(b_lean_obj_arg s1, b_lean_obj_arg s2) {
    return std::memcmp(lean_string_cstr(s1), lean_string_cstr(s2), lean_string_size(s1)) == 0;
}

bool string_eq(object * s1, char const * s2) {
    if (lean_string_size(s1) != strlen(s2) + 1)
        return false;
    return std::memcmp(lean_string_cstr(s1), s2, lean_string_size(s1)) == 0;
}

extern "C" LEAN_EXPORT bool lean_string_lt(object * s1, object * s2) {
    size_t sz1 = lean_string_size(s1) - 1; // ignore null char in the end
    size_t sz2 = lean_string_size(s2) - 1; // ignore null char in the end
    int r      = std::memcmp(lean_string_cstr(s1), lean_string_cstr(s2), std::min(sz1, sz2));
    return r < 0 || (r == 0 && sz1 < sz2);
}

static obj_res string_to_list_core(std::string const & s, bool reverse = false) {
    std::vector<unsigned> tmp;
    utf8_decode(s, tmp);
    if (reverse)
        std::reverse(tmp.begin(), tmp.end());
    obj_res  r = lean_box_uint32(0);
    unsigned i = tmp.size();
    while (i > 0) {
        --i;
        obj_res new_r = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(new_r, 0, lean_box_uint32(tmp[i]));
        lean_ctor_set(new_r, 1, r);
        r = new_r;
    }
    return r;
}

extern "C" LEAN_EXPORT obj_res lean_string_mk(obj_arg cs) {
    std::string s;
    b_obj_arg o = cs;
    size_t len = 0;
    while (!lean_is_scalar(o)) {
        push_unicode_scalar(s, lean_unbox_uint32(lean_ctor_get(o, 0)));
        o = lean_ctor_get(o, 1);
        len++;
    }
    lean_dec(cs);
    return lean_mk_string_unchecked(s.data(), s.size(), len);
}

extern "C" LEAN_EXPORT obj_res lean_string_data(obj_arg s) {
    std::string tmp = string_to_std(s);
    lean_dec_ref(s);
    return string_to_list_core(tmp);
}

static bool lean_string_utf8_get_core(char const * str, usize size, usize i, uint32 & result) {
    unsigned c = static_cast<unsigned char>(str[i]);
    /* zero continuation (0 to 0x7F) */
    if ((c & 0x80) == 0) {
        result = c;
        return true;
    }

    /* one continuation (0x80 to 0x7FF) */
    if ((c & 0xe0) == 0xc0 && i + 1 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        result = ((c & 0x1f) << 6) | (c1 & 0x3f);
        if (result >= 0x80) {
            return true;
        }
    }

    /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
    if ((c & 0xf0) == 0xe0 && i + 2 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned c2 = static_cast<unsigned char>(str[i+2]);
        result = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
        if (result >= 0x800 && (result < 0xD800 || result > 0xDFFF)) {
            return true;
        }
    }

    /* three continuations (0x10000 to 0x10FFFF) */
    if ((c & 0xf8) == 0xf0 && i + 3 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned c2 = static_cast<unsigned char>(str[i+2]);
        unsigned c3 = static_cast<unsigned char>(str[i+3]);
        result = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
        if (result >= 0x10000 && result <= 0x10FFFF) {
            return true;
        }
    }

    /* invalid UTF-8 encoded string */
    return false;
}

extern "C" LEAN_EXPORT uint32 lean_string_utf8_get(b_obj_arg s, b_obj_arg i0) {
    if (!lean_is_scalar(i0)) {
        /* If `i0` is not a scalar, then it must be > LEAN_MAX_SMALL_NAT,
           and should not be a valid index.

           Recall that LEAN_MAX_SMALL_NAT is 2^31-1 in 32-bit machines and
           2^63 - 1 in 64-bit ones.

           `i0` would only be a valid index if `s` had more than `LEAN_MAX_SMALL_NAT`
           bytes which is unlikely.

           For example, Linux for 64-bit machines can address at most 256 Tb which
           is less than 2^63 - 1.
        */
        return lean_char_default_value();
    }
    usize i = lean_unbox(i0);
    char const * str = lean_string_cstr(s);
    usize size = lean_string_size(s) - 1;
    if (i >= lean_string_size(s) - 1)
        return lean_char_default_value();
    uint32 result;
    if (lean_string_utf8_get_core(str, size, i, result))
        return result;
    else
        return lean_char_default_value();
}

extern "C" LEAN_EXPORT uint32_t lean_string_utf8_get_fast_cold(char const * str, size_t i, size_t size, unsigned char c) {
    /* one continuation (0x80 to 0x7FF) */
    if ((c & 0xe0) == 0xc0 && i + 1 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        uint32_t result = ((c & 0x1f) << 6) | (c1 & 0x3f);
        if (result >= 0x80) {
            return result;
        }
    }

    /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
    if ((c & 0xf0) == 0xe0 && i + 2 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned c2 = static_cast<unsigned char>(str[i+2]);
        uint32_t result = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
        if (result >= 0x800 && (result < 0xD800 || result > 0xDFFF)) {
            return result;
        }
    }

    /* three continuations (0x10000 to 0x10FFFF) */
    if ((c & 0xf8) == 0xf0 && i + 3 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned c2 = static_cast<unsigned char>(str[i+2]);
        unsigned c3 = static_cast<unsigned char>(str[i+3]);
        uint32_t result = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
        if (result >= 0x10000 && result <= 0x10FFFF) {
            return result;
        }
    }
  /* invalid UTF-8 encoded string */
  return lean_char_default_value();
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_get_opt(b_obj_arg s, b_obj_arg i0) {
    if (!lean_is_scalar(i0)) {
        return lean_box(0);
    }
    usize i = lean_unbox(i0);
    char const * str = lean_string_cstr(s);
    usize size = lean_string_size(s) - 1;
    if (i >= lean_string_size(s) - 1)
        return lean_box(0);
    uint32 result;
    if (lean_string_utf8_get_core(str, size, i, result)) {
        obj_res new_r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(new_r, 0, lean_box_uint32(result));
        return new_r;
    } else {
        return lean_box(0);
    }
}

static uint32 lean_string_utf8_get_panic() {
    lean_panic_fn(lean_box(0), lean_mk_ascii_string_unchecked("Error: invalid `String.Pos` at `String.get!`"));
    return lean_char_default_value();
}

extern "C" LEAN_EXPORT uint32 lean_string_utf8_get_bang(b_obj_arg s, b_obj_arg i0) {
    if (!lean_is_scalar(i0)) {
        return lean_string_utf8_get_panic();
    }
    usize i = lean_unbox(i0);
    char const * str = lean_string_cstr(s);
    usize size = lean_string_size(s) - 1;
    if (i >= lean_string_size(s) - 1)
        return lean_string_utf8_get_panic();
    uint32 result;
    if (lean_string_utf8_get_core(str, size, i, result))
        return result;
    else
        return lean_string_utf8_get_panic();
}


/* The reference implementation is:
   ```
   def next (s : @& String) (p : @& Pos) : Ppos :=
   let c := get s p in
   p + csize c
   ```
*/
extern "C" LEAN_EXPORT obj_res lean_string_utf8_next(b_obj_arg s, b_obj_arg i0) {
    if (!lean_is_scalar(i0)) {
        /* See comment at string_utf8_get */
        return lean_nat_add(i0, lean_box(1));
    }
    usize i = lean_unbox(i0);
    char const * str = lean_string_cstr(s);
    usize size       = lean_string_size(s) - 1;
    /* `csize c` is 1 when `i` is not a valid position in the reference implementation. */
    if (i >= size) return lean_box(i+1);
    unsigned c = static_cast<unsigned char>(str[i]);
    if ((c & 0x80) == 0)    return lean_box(i+1);
    if ((c & 0xe0) == 0xc0) return lean_box(i+2);
    if ((c & 0xf0) == 0xe0) return lean_box(i+3);
    if ((c & 0xf8) == 0xf0) return lean_box(i+4);
    /* invalid UTF-8 encoded string */
    return lean_box(i+1);
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_next_fast_cold(size_t i, unsigned char c) {
    if ((c & 0xe0) == 0xc0) return lean_box(i+2);
    if ((c & 0xf0) == 0xe0) return lean_box(i+3);
    if ((c & 0xf8) == 0xf0) return lean_box(i+4);
    /* invalid UTF-8 encoded string */
    return lean_box(i+1);
}

static inline bool is_utf8_first_byte(unsigned char c) {
    return (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 || (c & 0xf8) == 0xf0;
}

extern "C" LEAN_EXPORT uint8 lean_string_is_valid_pos(b_obj_arg s, b_obj_arg i0) {
    if (!lean_is_scalar(i0)) {
        /* See comment at string_utf8_get */
        return false;
    }
    usize i = lean_unbox(i0);
    usize sz = lean_string_size(s) - 1;
    if (i > sz) return false;
    if (i == sz) return true;
    char const * str = lean_string_cstr(s);
    return is_utf8_first_byte(str[i]);
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_extract(b_obj_arg s, b_obj_arg b0, b_obj_arg e0) {
    if (!lean_is_scalar(b0) || !lean_is_scalar(e0)) {
        /* See comment at string_utf8_get */
        return s;
    }
    usize b = lean_unbox(b0);
    usize e = lean_unbox(e0);
    char const * str = lean_string_cstr(s);
    usize sz = lean_string_size(s) - 1;
    if (b >= e || b >= sz) return lean_mk_string_unchecked("", 0, 0);
    /* In the reference implementation if `b` is not pointing to a valid UTF8
       character start position, the result is the empty string. */
    if (!is_utf8_first_byte(str[b])) return lean_mk_string_unchecked("", 0, 0);
    if (e > sz) e = sz;
    lean_assert(b < e);
    lean_assert(e > 0);
    /* In the reference implementation if `e` is not pointing to a valid UTF8
       character start position, it is assumed to be at the end. */
    if (e < sz && !is_utf8_first_byte(str[e])) e = sz;
    usize new_sz = e - b;
    lean_assert(new_sz > 0);
    return lean_mk_string_from_bytes_unchecked(lean_string_cstr(s) + b, new_sz);
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_prev(b_obj_arg s, b_obj_arg i0) {
    if (!lean_is_scalar(i0)) {
        /* See comment at string_utf8_get */
        return lean_nat_sub(i0, lean_box(1));
    }
    usize i  = lean_unbox(i0);
    usize sz = lean_string_size(s) - 1;
    if (i == 0 || i > sz) return lean_box(0);
    i--;
    char const * str = lean_string_cstr(s);
    while (!is_utf8_first_byte(str[i])) {
        lean_assert(i > 0);
        i--;
    }
    return lean_box(i);
}

static unsigned get_utf8_char_size_at(std::string const & s, usize i) {
    if (auto sz = get_utf8_first_byte_opt(s[i])) {
        return *sz;
    } else {
        return 1;
    }
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_set(obj_arg s, b_obj_arg i0, uint32 c) {
    if (!lean_is_scalar(i0)) {
        /* See comment at string_utf8_get */
        return s;
    }
    usize i  = lean_unbox(i0);
    usize sz = lean_string_size(s) - 1;
    if (i >= sz) return s;
    char * str = w_string_cstr(s);
    if (lean_is_exclusive(s)) {
        if (static_cast<unsigned char>(str[i]) < 128 && c < 128) {
            str[i] = c;
            return s;
        }
    }
    if (!is_utf8_first_byte(str[i])) return s;
    /* TODO(Leo): improve performance of other special cases.
       Example: is_exclusive(s) and new and old characters have the same size; etc. */
    std::string tmp;
    push_unicode_scalar(tmp, c);
    std::string new_s = string_to_std(s);
    usize len = lean_string_len(s);
    dec(s);
    new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
    return lean_mk_string_unchecked(new_s.data(), new_s.size(), len);
}

extern "C" LEAN_EXPORT uint64 lean_string_hash(b_obj_arg s) {
    usize sz = lean_string_size(s) - 1;
    char const * str = lean_string_cstr(s);
    return hash_str(sz, (unsigned char const *) str, 11);
}

extern "C" LEAN_EXPORT obj_res lean_string_of_usize(size_t n) {
    return mk_ascii_string_unchecked(std::to_string(n));
}

// =======================================
// ByteArray & FloatArray

size_t lean_nat_to_size_t(obj_arg n) {
    if (lean_is_scalar(n)) {
        return lean_unbox(n);
    } else {
        mpz const & v = mpz_value(n);
        if (!v.is_size_t()) lean_internal_panic_out_of_memory();
        size_t sz = v.get_size_t();
        lean_dec(n);
        return sz;
    }
}

extern "C" LEAN_EXPORT obj_res lean_copy_sarray(obj_arg a, size_t cap) {
    unsigned esz   = lean_sarray_elem_size(a);
    size_t sz      = lean_sarray_size(a);
    lean_assert(cap >= sz);
    object * r     = lean_alloc_sarray(esz, sz, cap);
    uint8 * it     = lean_sarray_cptr(a);
    uint8 * dest   = lean_sarray_cptr(r);
    memcpy(dest, it, esz*sz);
    lean_dec(a);
    return r;
}

obj_res lean_sarray_ensure_exclusive(obj_arg a) {
    if (lean_is_exclusive(a)) {
        return a;
    } else {
        return lean_copy_sarray(a, lean_sarray_capacity(a));
    }
}

/* Ensure that `a` has capacity at least `min_cap`, copying `a` otherwise.
   If `exact` is false, double the capacity on copying. */
extern "C" LEAN_EXPORT obj_res lean_sarray_ensure_capacity(obj_arg a, size_t min_cap, bool exact) {
    size_t cap = lean_sarray_capacity(a);
    if (min_cap <= cap) {
        return a;
    } else {
        return lean_copy_sarray(a, exact ? min_cap : min_cap * 2);
    }
}

extern "C" LEAN_EXPORT obj_res lean_copy_byte_array(obj_arg a) {
    return lean_copy_sarray(a, lean_sarray_capacity(a));
}

extern "C" LEAN_EXPORT obj_res lean_byte_array_mk(obj_arg a) {
    usize sz      = lean_array_size(a);
    obj_res r     = lean_alloc_sarray(1, sz, sz);
    object ** it  = lean_array_cptr(a);
    object ** end = it + sz;
    uint8 * dest  = lean_sarray_cptr(r);
    for (; it != end; ++it, ++dest) {
        *dest = lean_unbox(*it);
    }
    lean_dec(a);
    return r;
}

extern "C" LEAN_EXPORT obj_res lean_byte_array_data(obj_arg a) {
    usize sz       = lean_sarray_size(a);
    obj_res r      = lean_alloc_array(sz, sz);
    uint8 * it     = lean_sarray_cptr(a);
    uint8 * end    = it+sz;
    object ** dest = lean_array_cptr(r);
    for (; it != end; ++it, ++dest) {
        *dest = lean_box(*it);
    }
    lean_dec(a);
    return r;
}

extern "C" LEAN_EXPORT obj_res lean_byte_array_push(obj_arg a, uint8 b) {
    object * r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(a, lean_sarray_size(a) + 1, /* exact */ false));
    size_t & sz  = lean_to_sarray(r)->m_size;
    uint8 * it   = lean_sarray_cptr(r) + sz;
    *it = b;
    sz++;
    return r;
}

    extern "C" LEAN_EXPORT obj_res lean_byte_array_copy_slice(b_obj_arg src, obj_arg o_src_off, obj_arg dest, obj_arg o_dest_off, obj_arg o_len, bool exact) {
    size_t ssz = lean_sarray_size(src);
    size_t dsz = lean_sarray_size(dest);
    size_t src_off = lean_nat_to_size_t(o_src_off);
    if (src_off > ssz) {
        return dest;
    }
    size_t len = std::min(lean_nat_to_size_t(o_len), ssz - src_off);
    size_t dest_off = lean_nat_to_size_t(o_dest_off);
    if (dest_off > dsz) {
        dest_off = dsz;
    }
    size_t new_dsz = std::max(dsz, dest_off + len);
    object * r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(dest, new_dsz, exact));
    lean_to_sarray(r)->m_size = new_dsz;
    // `r` is exclusive, so the ranges definitely cannot overlap
    memcpy(lean_sarray_cptr(r) + dest_off, lean_sarray_cptr(src) + src_off, len);
    return r;
}

extern "C" LEAN_EXPORT uint64_t lean_byte_array_hash(b_obj_arg a) {
    return hash_str(lean_sarray_size(a), lean_sarray_cptr(a), 11);
}

extern "C" LEAN_EXPORT obj_res lean_copy_float_array(obj_arg a) {
    return lean_copy_sarray(a, lean_sarray_capacity(a));
}

extern "C" LEAN_EXPORT obj_res lean_float_array_mk(obj_arg a) {
    usize sz      = lean_array_size(a);
    obj_res r     = lean_alloc_sarray(sizeof(double), sz, sz); // NOLINT
    object ** it  = lean_array_cptr(a);
    object ** end = it + sz;
    double * dest = reinterpret_cast<double*>(lean_sarray_cptr(r));
    for (; it != end; ++it, ++dest) {
        *dest = lean_unbox_float(*it);
    }
    lean_dec(a);
    return r;
}

extern "C" LEAN_EXPORT obj_res lean_float_array_data(obj_arg a) {
    usize sz       = lean_sarray_size(a);
    obj_res r      = lean_alloc_array(sz, sz);
    double * it    = reinterpret_cast<double*>(lean_sarray_cptr(a));
    double * end   = it+sz;
    object ** dest = lean_array_cptr(r);
    for (; it != end; ++it, ++dest) {
        *dest = lean_box_float(*it);
    }
    lean_dec(a);
    return r;
}

extern "C" LEAN_EXPORT obj_res lean_float_array_push(obj_arg a, double d) {
    object * r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(a, lean_sarray_size(a) + 1, /* exact */ false));
    size_t & sz  = lean_to_sarray(r)->m_size;
    double * it  = reinterpret_cast<double*>(lean_sarray_cptr(r)) + sz;
    *it = d;
    sz++;
    return r;
}

// =======================================
// Array functions for generated code

extern "C" LEAN_EXPORT object * lean_mk_array(obj_arg n, obj_arg v) {
    size_t sz;
    if (lean_is_scalar(n)) {
        sz = lean_unbox(n);
    } else {
        mpz const & v = mpz_value(n);
        if (!v.is_size_t()) lean_internal_panic_out_of_memory();
        sz = v.get_size_t();
        lean_dec(n);
    }
    object * r    = lean_alloc_array(sz, sz);
    object ** it  = lean_array_cptr(r);
    object ** end = it + sz;
    for (; it != end; ++it) {
        *it = v;
    }
    if (sz == 0) {
        lean_dec(v);
    } else if (sz > 1) {
        lean_inc_n(v, sz - 1);
    }
    return r;
}

extern "C" LEAN_EXPORT obj_res lean_copy_expand_array(obj_arg a, bool expand) {
    size_t sz      = lean_array_size(a);
    size_t cap     = lean_array_capacity(a);
    lean_assert(cap >= sz);
    if (expand) cap = (cap + 1) * 2;
    lean_assert(!expand || cap > sz);
    object * r     = lean_alloc_array(sz, cap);
    object ** it   = lean_array_cptr(a);
    object ** end  = it + sz;
    object ** dest = lean_array_cptr(r);
    if (lean_is_exclusive(a)) {
        // transfer ownership of elements directly instead of inc+dec
        memcpy(dest, it, sz * sizeof(object *));
        lean_dealloc(a, lean_array_byte_size(a));
    } else {
        for (; it != end; ++it, ++dest) {
            *dest = *it;
            lean_inc(*it);
        }
        lean_dec(a);
    }
    return r;
}

extern "C" LEAN_EXPORT object * lean_array_push(obj_arg a, obj_arg v) {
    object * r;
    if (lean_is_exclusive(a)) {
        if (lean_array_capacity(a) > lean_array_size(a))
            r = a;
        else
            r = lean_copy_expand_array(a, true);
    } else {
        r = lean_copy_expand_array(a, lean_array_capacity(a) < 2*lean_array_size(a) + 1);
    }
    lean_assert(lean_array_capacity(r) > lean_array_size(r));
    size_t & sz  = lean_to_array(r)->m_size;
    object ** it = lean_array_cptr(r) + sz;
    *it = v;
    sz++;
    return r;
}

// =======================================
// Name primitives

extern "C" LEAN_EXPORT uint8 lean_name_eq(b_lean_obj_arg n1, b_lean_obj_arg n2) {
    if (n1 == n2)
        return true;
    if (lean_is_scalar(n1) != lean_is_scalar(n2) || lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2))
        return false;
    while (true) {
        lean_assert(!lean_is_scalar(n1));
        lean_assert(!lean_is_scalar(n2));
        lean_assert(n1 && n2);
        if (lean_ptr_tag(n1) != lean_ptr_tag(n2))
            return false;
        if (lean_ptr_tag(n1) == 1) {
            if (!lean_string_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)))
                return false;
        } else {
            if (!lean_nat_eq(lean_ctor_get(n1, 1), lean_ctor_get(n1, 1)))
                return false;
        }
        n1 = lean_ctor_get(n1, 0);
        n2 = lean_ctor_get(n2, 0);
        if (n1 == n2)
            return true;
        if (lean_is_scalar(n1) != lean_is_scalar(n2))
            return false;
        /*
        // The `return false` in the following `if` is seldom reached.
        if (lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2))
            return false;
        */
    }
}

// =======================================
// Runtime info

extern "C" LEAN_EXPORT object * lean_closure_max_args(object *) {
    return lean_unsigned_to_nat((unsigned)LEAN_CLOSURE_MAX_ARGS);
}

extern "C" LEAN_EXPORT object * lean_max_small_nat(object *) {
    return lean_usize_to_nat(LEAN_MAX_SMALL_NAT);
}

// =======================================
// Debugging helper functions

extern "C" obj_res lean_io_eprintln(obj_arg s, obj_arg w);
void io_eprintln(obj_arg s) {
    object * r = lean_io_eprintln(s, lean_io_mk_world());
    lean_assert(lean_io_result_is_ok(r));
    lean_dec(r);
}

extern "C" LEAN_EXPORT object * lean_dbg_trace(obj_arg s, obj_arg fn) {
    io_eprintln(s);
    return lean_apply_1(fn, lean_box(0));
}

extern "C" LEAN_EXPORT object * lean_dbg_sleep(uint32 ms, obj_arg fn) {
    chrono::milliseconds c(ms);
    this_thread::sleep_for(c);
    return lean_apply_1(fn, lean_box(0));
}

extern "C" LEAN_EXPORT object * lean_dbg_trace_if_shared(obj_arg s, obj_arg a) {
    if (!lean_is_scalar(a) && lean_is_shared(a)) {
        io_eprintln(mk_string(std::string("shared RC ") + lean_string_cstr(s)));
    }
    return a;
}

extern "C" LEAN_EXPORT object * lean_dbg_stack_trace(obj_arg fn) {
    print_backtrace(/* force_stderr */ false);
    return lean_apply_1(fn, lean_box(0));
}

// =======================================
// Module initialization

static std::vector<lean_external_class*> * g_ext_classes;
static mutex                             * g_ext_classes_mutex;

extern "C" LEAN_EXPORT lean_external_class * lean_register_external_class(lean_external_finalize_proc p1, lean_external_foreach_proc p2) {
    unique_lock<mutex> lock(*g_ext_classes_mutex);
    external_object_class * cls = new external_object_class{p1, p2};
    g_ext_classes->push_back(cls);
    return cls;
}

void initialize_object() {
    g_ext_classes       = new std::vector<external_object_class*>();
    g_ext_classes_mutex = new mutex();
    g_array_empty       = lean_alloc_array(0, 0);
    mark_persistent(g_array_empty);
}

void finalize_object() {
    for (external_object_class * cls : *g_ext_classes) delete cls;
    delete g_ext_classes;
    delete g_ext_classes_mutex;
}
}
