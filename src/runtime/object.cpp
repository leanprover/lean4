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
#include "runtime/mpq.h"
#include "runtime/thread.h"
#include "runtime/utf8.h"
#include "runtime/alloc.h"
#include "runtime/debug.h"
#include "runtime/hash.h"
#include "runtime/flet.h"
#include "runtime/interrupt.h"
#include "runtime/buffer.h"

// see `Task.Priority.max`
#define LEAN_MAX_PRIO 8

namespace lean {
extern "C" LEAN_EXPORT void lean_internal_panic(char const * msg) {
    std::cerr << "INTERNAL PANIC: " << msg << "\n";
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

extern "C" LEAN_EXPORT object * lean_panic_fn(object * default_val, object * msg) {
    // TODO(Leo, Kha): add thread local buffer for interpreter.
    if (g_panic_messages) {
        std::cerr << lean_string_cstr(msg) << "\n";
    }
#ifndef LEAN_EMSCRIPTEN
    if (std::getenv("LEAN_ABORT_ON_PANIC")) {
        int * v = nullptr;
        *v = 0;
    }
#endif
    if (g_exit_on_panic) {
        std::exit(1);
    }
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

static inline void lean_dealloc(lean_object * o, size_t sz) {
#ifdef LEAN_SMALL_ALLOCATOR
    dealloc(o, sz);
#else
    free(o);
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
extern "C" object * lean_array_to_list(object *, object *);

extern "C" LEAN_EXPORT object * lean_array_mk(lean_obj_arg lst) {
    return lean_list_to_array(lean_box(0), lst);
}

extern "C" LEAN_EXPORT lean_object * lean_array_data(lean_obj_arg a) {
    return lean_array_to_list(lean_box(0), a);
}

extern "C" LEAN_EXPORT lean_obj_res lean_array_get_panic(lean_obj_arg def_val) {
    return lean_panic_fn(def_val, lean_mk_string("Error: index out of bounds"));
}

extern "C" LEAN_EXPORT lean_obj_res lean_array_set_panic(lean_obj_arg a, lean_obj_arg v) {
    lean_dec(v);
    return lean_panic_fn(a, lean_mk_string("Error: index out of bounds"));
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
// Fixpoint

static inline object * ptr_to_weak_ptr(object * p) {
    return reinterpret_cast<object*>(reinterpret_cast<uintptr_t>(p) | 1);
}

static inline object * weak_ptr_to_ptr(object * w) {
    return reinterpret_cast<object*>((reinterpret_cast<uintptr_t>(w) >> 1) << 1);
}

obj_res fixpoint_aux(obj_arg rec, obj_arg weak_k, obj_arg a) {
    object * k = weak_ptr_to_ptr(weak_k);
    lean_inc(k);
    return lean_apply_2(rec, k, a);
}

extern "C" LEAN_EXPORT obj_res lean_fixpoint(obj_arg rec, obj_arg a) {
    object * k = lean_alloc_closure((void*)fixpoint_aux, 3, 2);
    lean_inc(rec);
    lean_closure_set(k, 0, rec);
    lean_closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = lean_apply_2(rec, k, a);
    return r;
}

obj_res fixpoint_aux2(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2) {
    object * k = weak_ptr_to_ptr(weak_k);
    lean_inc(k);
    return lean_apply_3(rec, k, a1, a2);
}

extern "C" LEAN_EXPORT obj_res lean_fixpoint2(obj_arg rec, obj_arg a1, obj_arg a2) {
    object * k = lean_alloc_closure((void*)fixpoint_aux2, 4, 2);
    lean_inc(rec);
    lean_closure_set(k, 0, rec);
    lean_closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = lean_apply_3(rec, k, a1, a2);
    return r;
}

obj_res fixpoint_aux3(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2, obj_arg a3) {
    object * k = weak_ptr_to_ptr(weak_k);
    lean_inc(k);
    return lean_apply_4(rec, k, a1, a2, a3);
}

extern "C" LEAN_EXPORT obj_res lean_fixpoint3(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3) {
    object * k = lean_alloc_closure((void*)fixpoint_aux3, 5, 2);
    lean_inc(rec);
    lean_closure_set(k, 0, rec);
    lean_closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = lean_apply_4(rec, k, a1, a2, a3);
    return r;
}

obj_res fixpoint_aux4(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4) {
    object * k = weak_ptr_to_ptr(weak_k);
    lean_inc(k);
    return lean_apply_5(rec, k, a1, a2, a3, a4);
}

extern "C" LEAN_EXPORT obj_res lean_fixpoint4(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4) {
    object * k = lean_alloc_closure((void*)fixpoint_aux4, 6, 2);
    lean_inc(rec);
    lean_closure_set(k, 0, rec);
    lean_closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = lean_apply_5(rec, k, a1, a2, a3, a4);
    return r;
}

obj_res fixpoint_aux5(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5) {
    object * k = weak_ptr_to_ptr(weak_k);
    lean_inc(k);
    return lean_apply_6(rec, k, a1, a2, a3, a4, a5);
}

extern "C" LEAN_EXPORT obj_res lean_fixpoint5(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5) {
    object * k = lean_alloc_closure((void*)fixpoint_aux5, 7, 2);
    lean_inc(rec);
    lean_closure_set(k, 0, rec);
    lean_closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = lean_apply_6(rec, k, a1, a2, a3, a4, a5);
    return r;
}

obj_res fixpoint_aux6(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5, obj_arg a6) {
    object * k = weak_ptr_to_ptr(weak_k);
    lean_inc(k);
    return lean_apply_7(rec, k, a1, a2, a3, a4, a5, a6);
}

extern "C" LEAN_EXPORT obj_res lean_fixpoint6(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5, obj_arg a6) {
    object * k = lean_alloc_closure((void*)fixpoint_aux6, 8, 2);
    lean_inc(rec);
    lean_closure_set(k, 0, rec);
    lean_closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = lean_apply_7(rec, k, a1, a2, a3, a4, a5, a6);
    return r;
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
    unsigned                                      m_num_std_workers{0};
    unsigned                                      m_max_std_workers{0};
    unsigned                                      m_num_dedicated_workers{0};
    std::deque<lean_task_object *>                m_queues[LEAN_MAX_PRIO+1];
    unsigned                                      m_queues_size{0};
    unsigned                                      m_max_prio{0};
    condition_variable                            m_queue_cv;
    condition_variable                            m_task_finished_cv;
    condition_variable                            m_worker_finished_cv;
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

    void enqueue_core(lean_task_object * t) {
        lean_assert(t->m_imp);
        unsigned prio = t->m_imp->m_prio;
        if (prio > LEAN_MAX_PRIO) {
            spawn_dedicated_worker(t);
            return;
        }
        if (prio > m_max_prio)
            m_max_prio = prio;
        m_queues[prio].push_back(t);
        m_queues_size++;
        if (m_num_std_workers < m_max_std_workers)
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
        m_num_std_workers++;
        lthread([this]() {
            save_stack_info(false);
            unique_lock<mutex> lock(m_mutex);
            while (true) {
                if (m_queues_size == 0) {
                    if (m_shutting_down) {
                        break;
                    }
                    m_queue_cv.wait(lock);
                    continue;
                }

                lean_task_object * t = dequeue();
                run_task(lock, t);
                reset_heartbeat();
            }
            m_num_std_workers--;
            m_worker_finished_cv.notify_all();
        });
        // `lthread` will be implicitly freed, which frees up its control resources but does not terminate the thread
    }

    void spawn_dedicated_worker(lean_task_object * t) {
        m_num_dedicated_workers++;
        lthread([this, t]() {
            save_stack_info(false);
            unique_lock<mutex> lock(m_mutex);
            run_task(lock, t);
            m_num_dedicated_workers--;
            m_worker_finished_cv.notify_all();
        });
        // see above
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
            handle_finished(t);
            mark_mt(v);
            t->m_value = v;
            /* After the task has been finished and we propagated
               dependecies, we can release `m_imp` and keep just the value */
            free_task_imp(t->m_imp);
            t->m_imp   = nullptr;
            m_task_finished_cv.notify_all();
        } else {
            // `bind` task has not finished yet, re-add as dependency of nested task
            lock.unlock();
            add_dep(lean_to_task(closure_arg_cptr(t->m_imp->m_closure)[0]), t);
            lock.lock();
        }
    }

    void handle_finished(lean_task_object * t) {
        lean_task_object * it = t->m_imp->m_head_dep;
        t->m_imp->m_head_dep = nullptr;
        while (it) {
            if (t->m_imp->m_canceled)
                it->m_imp->m_canceled = true;
            lean_task_object * next_it = it->m_imp->m_next_dep;
            it->m_imp->m_next_dep = nullptr;
            if (it->m_imp->m_deleted) {
                free_task(it);
            } else {
                enqueue_core(it);
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
        unique_lock<mutex> lock(m_mutex);
        m_shutting_down = true;
        m_queue_cv.notify_all();
        // wait for all workers to finish
        m_worker_finished_cv.wait(lock, [&]() { return m_num_std_workers + m_num_dedicated_workers == 0; });
    }

    void enqueue(lean_task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        enqueue_core(t);
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
            enqueue_core(t2);
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
        m_task_finished_cv.wait(lock, [&]() { return t->m_value != nullptr; });
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
    g_task_manager = new task_manager(num_workers);
#endif
}

extern "C" LEAN_EXPORT void lean_init_task_manager() {
    lean_init_task_manager_using(hardware_concurrency());
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

extern "C" LEAN_EXPORT obj_res lean_task_map_core(obj_arg f, obj_arg t, unsigned prio, bool keep_alive) {
    if (!g_task_manager) {
        return lean_task_pure(apply_1(f, lean_task_get_own(t)));
    } else {
        lean_task_object * new_task = alloc_task(mk_closure_3_2(task_map_fn, f, t), prio, keep_alive);
        g_task_manager->add_dep(lean_to_task(t), new_task);
        return (lean_object*)new_task;
    }
}

extern "C" LEAN_EXPORT b_obj_res lean_task_get(b_obj_arg t) {
    if (object * v = lean_to_task(t)->m_value)
        return v;
    g_task_manager->wait_for(lean_to_task(t));
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

extern "C" LEAN_EXPORT obj_res lean_task_bind_core(obj_arg x, obj_arg f, unsigned prio, bool keep_alive) {
    if (!g_task_manager) {
        return apply_1(f, lean_task_get_own(x));
    } else {
        lean_task_object * new_task = alloc_task(mk_closure_3_2(task_bind_fn1, x, f), prio, keep_alive);
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

extern "C" LEAN_EXPORT bool lean_io_has_finished_core(b_obj_arg t) {
    return lean_to_task(t)->m_value != nullptr;
}

extern "C" LEAN_EXPORT b_obj_res lean_io_wait_any_core(b_obj_arg task_list) {
    return g_task_manager->wait_any(task_list);
}

// =======================================
// Natural numbers

object * alloc_mpz(mpz const & m) {
    void * mem = lean_alloc_small_object(sizeof(mpz_object));
    mpz_object * o = new (mem) mpz_object(m);
    lean_set_st_header((lean_object*)o, LeanMPZ, 0);
    return (lean_object*)o;
}

extern "C" LEAN_EXPORT lean_object * lean_alloc_mpz(mpz_t v) {
    return alloc_mpz(mpz(v));
}

extern "C" LEAN_EXPORT void lean_extract_mpz_value(lean_object * o, mpz_t v) {
    return to_mpz(o)->m_value.set(v);
}

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
            return lean_box((mpz_value(a1) % mpz::of_size_t(n2)).get_unsigned_int());
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
    mpz r;
    mod2k(r, mpz_value(a), 8);
    return static_cast<uint8>(r.get_unsigned_int());
}

extern "C" LEAN_EXPORT uint16 lean_uint16_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 16);
    return static_cast<uint16>(r.get_unsigned_int());
}

extern "C" LEAN_EXPORT uint32 lean_uint32_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 32);
    return static_cast<uint32>(r.get_unsigned_int());
}

extern "C" LEAN_EXPORT uint32 lean_uint32_big_modn(uint32 a1, b_lean_obj_arg a2) {
    mpz const & m = mpz_value(a2);
    return m.is_unsigned_int() ? a1 % m.get_unsigned_int() : a1;
}

extern "C" LEAN_EXPORT uint64 lean_uint64_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 64);
    if (sizeof(void*) == 8) {
        // 64 bit
        return static_cast<uint64>(r.get_size_t());
    } else {
        // 32 bit
        mpz l;
        mod2k(l, r, 32);
        mpz h;
        div2k(h, r, 32);
        return (static_cast<uint64>(h.get_unsigned_int()) << 32) + static_cast<uint64>(l.get_unsigned_int());
    }
}

extern "C" LEAN_EXPORT uint64 lean_uint64_big_modn(uint64 a1, b_lean_obj_arg) {
    // TODO(Leo)
    return a1;
}

extern "C" LEAN_EXPORT uint64 lean_uint64_mix_hash(uint64 a1, uint64 a2) {
  return hash(a1, a2);
}

extern "C" LEAN_EXPORT usize lean_usize_of_big_nat(b_obj_arg a) {
    return mpz_value(a).get_size_t();
}

extern "C" LEAN_EXPORT usize lean_usize_big_modn(usize a1, b_lean_obj_arg) {
    // TODO(Leo)
    return a1;
}

extern "C" LEAN_EXPORT usize lean_usize_mix_hash(usize a1, usize a2) {
    if (sizeof(void*) == 8)
        return hash(static_cast<uint64>(a1), static_cast<uint64>(a2));
    else
        return hash(static_cast<uint32>(a1), static_cast<uint32>(a2));
}

// =======================================
// Float

extern "C" LEAN_EXPORT double lean_float_of_nat(b_lean_obj_arg a) {
    if (lean_is_scalar(a)) {
        return static_cast<double>(lean_unbox(a));
    } else {
        return mpz_value(a).get_double();
    }
}

extern "C" LEAN_EXPORT lean_obj_res lean_float_to_string(double a) {
    return mk_string(std::to_string(a));
}

static double of_scientific(mpz const & m, bool sign, size_t e) {
    if (sign)
        return (mpq(m)/mpz(10).pow(e)).get_double();
    else
        return (mpq(m)*mpz(10).pow(e)).get_double();
}

extern "C" LEAN_EXPORT double lean_float_of_scientific(b_lean_obj_arg m, uint8 esign, b_lean_obj_arg e) {
    if (!lean_is_scalar(e)) {
        if (esign) {
            return 0.0;
        } else {
            return std::numeric_limits<double>::infinity();
        }
    }
    if (lean_is_scalar(m)) {
        return of_scientific(mpz::of_size_t(lean_unbox(m)), esign, lean_unbox(e));
    } else {
        return of_scientific(mpz_value(m), esign, lean_unbox(e));
    }
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

extern "C" LEAN_EXPORT object * lean_mk_string(char const * s) {
    size_t sz  = strlen(s);
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = lean_alloc_string(rsz, rsz, len);
    memcpy(w_string_cstr(r), s, sz+1);
    return r;
}

extern "C" LEAN_EXPORT obj_res lean_string_from_utf8_unchecked(b_obj_arg a) {
    size_t sz  = lean_sarray_size(a);
    size_t len = utf8_strlen(reinterpret_cast<char *>(lean_sarray_cptr(a)), sz);
    size_t rsz = sz + 1;
    obj_res r  = lean_alloc_string(rsz, rsz, len);
    memcpy(w_string_cstr(r), lean_sarray_cptr(a), sz);
    w_string_cstr(r)[sz] = 0;
    return r;
}

extern "C" LEAN_EXPORT obj_res lean_string_to_utf8(b_obj_arg s) {
    size_t sz = lean_string_size(s) - 1;
    obj_res r = lean_alloc_sarray(1, sz, sz);
    memcpy(lean_sarray_cptr(r), lean_string_cstr(s), sz);
    return r;
}

object * mk_string(std::string const & s) {
    size_t sz  = s.size();
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = lean_alloc_string(rsz, rsz, len);
    memcpy(w_string_cstr(r), s.data(), sz);
    w_string_cstr(r)[sz] = 0;
    return r;
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
    unsigned new_sz = sz1 + sz2 - 1;
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

static std::string list_as_string(b_obj_arg lst) {
    std::string s;
    b_obj_arg o = lst;
    while (!lean_is_scalar(o)) {
        push_unicode_scalar(s, lean_unbox_uint32(lean_ctor_get(o, 0)));
        o = lean_ctor_get(o, 1);
    }
    return s;
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
    std::string s = list_as_string(cs);
    lean_dec(cs);
    return mk_string(s);
}

extern "C" LEAN_EXPORT obj_res lean_string_data(obj_arg s) {
    std::string tmp = string_to_std(s);
    lean_dec_ref(s);
    return string_to_list_core(tmp);
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
    unsigned c = static_cast<unsigned char>(str[i]);
    /* zero continuation (0 to 127) */
    if ((c & 0x80) == 0) {
        i++;
        return c;
    }

    /* one continuation (128 to 2047) */
    if ((c & 0xe0) == 0xc0 && i + 1 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned r = ((c & 0x1f) << 6) | (c1 & 0x3f);
        if (r >= 128) {
            i += 2;
            return r;
        }
    }

    /* two continuations (2048 to 55295 and 57344 to 65535) */
    if ((c & 0xf0) == 0xe0 && i + 2 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned c2 = static_cast<unsigned char>(str[i+2]);
        unsigned r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
        if (r >= 2048 && (r < 55296 || r > 57343)) {
            i += 3;
            return r;
        }
    }

    /* three continuations (65536 to 1114111) */
    if ((c & 0xf8) == 0xf0 && i + 3 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned c2 = static_cast<unsigned char>(str[i+2]);
        unsigned c3 = static_cast<unsigned char>(str[i+3]);
        unsigned r  = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
        if (r >= 65536 && r <= 1114111) {
            i += 4;
            return r;
        }
    }

    /* invalid UTF-8 encoded string */
    return lean_char_default_value();
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

static inline bool is_utf8_first_byte(unsigned char c) {
    return (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 || (c & 0xf8) == 0xf0;
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
    if (b >= e || b >= sz) return lean_mk_string("");
    /* In the reference implementation if `b` is not pointing to a valid UTF8
       character start position, the result is the empty string. */
    if (!is_utf8_first_byte(str[b])) return lean_mk_string("");
    if (e > sz) e = sz;
    lean_assert(b < e);
    lean_assert(e > 0);
    /* In the reference implementation if `e` is not pointing to a valid UTF8
       character start position, it is assumed to be at the end. */
    if (e < sz && !is_utf8_first_byte(str[e])) e = sz;
    usize new_sz = e - b;
    lean_assert(new_sz > 0);
    obj_res r = lean_alloc_string(new_sz+1, new_sz+1, 0);
    memcpy(w_string_cstr(r), lean_string_cstr(s) + b, new_sz);
    w_string_cstr(r)[new_sz] = 0;
    lean_to_string(r)->m_length = utf8_strlen(w_string_cstr(r), new_sz);
    return r;
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
    dec(s);
    new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
    return mk_string(new_s);
}

extern "C" LEAN_EXPORT uint64 lean_string_hash(b_obj_arg s) {
    usize sz = lean_string_size(s) - 1;
    char const * str = lean_string_cstr(s);
    return hash_str(sz, str, 11);
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
        lean_dec(*dest);
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
    for (; it != end; ++it, ++dest) {
        *dest = *it;
        lean_inc(*it);
    }
    lean_dec(a);
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
        lean_assert(lean_name_hash_ptr(n1) == lean_name_hash_ptr(n2));
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
        if (lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2))
            return false;
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
    if (lean_is_shared(a)) {
        io_eprintln(mk_string(std::string("shared RC ") + lean_string_cstr(s)));
    }
    return a;
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
