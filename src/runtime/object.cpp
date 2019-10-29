/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include <vector>
#include <deque>
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/utf8.h"
#include "runtime/alloc.h"
#include "runtime/debug.h"
#include "runtime/hash.h"
#include "runtime/flet.h"
#include "runtime/interrupt.h"
#include "util/buffer.h" // move to runtime

#define LEAN_MAX_PRIO 8

namespace lean {
extern "C" void lean_panic(char const * msg) {
    std::cerr << msg << "\n";
    lean_unreachable();
    std::exit(1);
}

extern "C" void lean_panic_out_of_memory() {
    lean_panic("out of memory");
}

extern "C" void lean_panic_unreachable() {
    lean_panic("unreachable code has been reached");
}

extern "C" void lean_panic_rc_overflow() {
    lean_panic("reference counter overflowed");
}

extern "C" object * lean_panic_fn(object * msg) {
    lean_panic(lean_string_cstr(msg));
}

extern "C" size_t lean_object_byte_size(lean_object * o) {
    if (lean_is_mt(o) || lean_is_st(o) || lean_is_persistent(o)) {
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
        default:
            /* For potentially big objects, we cannot store the size in the RC field when `defined(LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC)`.
               In this case, the RC is 32-bits, and it is not enough for big arrays/strings.
               Thus, we compute them using the respective *_byte_size operations. */
#if defined(LEAN_COMPRESSED_OBJECT_HEADER) || defined(LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC)
            return o->m_header & ((1ull << LEAN_RC_NBITS) - 1);
#else
            return o->m_rc;
#endif
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

extern "C" void lean_free_object(lean_object * o) {
    switch (lean_ptr_tag(o)) {
    case LeanArray:       return lean_dealloc(o, lean_array_byte_size(o));
    case LeanScalarArray: return lean_dealloc(o, lean_sarray_byte_size(o));
    case LeanString:      return lean_dealloc(o, lean_string_byte_size(o));
    case LeanMPZ:         to_mpz(o)->m_value.~mpz(); return lean_free_small_object(o);
    default:              return lean_free_small_object(o);
    }
}

static inline lean_object * get_next(lean_object * o) {
#if defined(LEAN_COMPRESSED_OBJECT_HEADER) || defined(LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC)
    size_t header = o->m_header;
    LEAN_BYTE(header, 6) = 0;
    LEAN_BYTE(header, 7) = 0;
    return (lean_object*)(header);
#else
    return (lean_object*)((size_t)(o->m_rc));
#endif
}

static inline void set_next(lean_object * o, lean_object * n) {
#if defined(LEAN_COMPRESSED_OBJECT_HEADER) || defined(LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC)
    size_t new_header = (size_t)n;
    LEAN_BYTE(new_header, 6) = LEAN_BYTE(o->m_header, 6);
    LEAN_BYTE(new_header, 7) = LEAN_BYTE(o->m_header, 7);
    o->m_header = new_header;
#else
    o->m_rc = (size_t)n;
#endif
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
    if (!lean_is_scalar(o) && lean_dec_ref_core(o))
        push_back(todo, o);
}

#ifdef LEAN_LAZY_RC
LEAN_THREAD_PTR(object, g_to_free);
#endif

static void lean_del_core(object * o, object * & todo);

extern "C" lean_object * lean_alloc_object(size_t sz) {
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
    if (r == nullptr) lean_panic_out_of_memory();
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

extern "C" void lean_del(object * o) {
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

extern "C" object * lean_array_mk(object * sz, object * fn) {
    if (!lean_is_scalar(sz)) {
        lean_dec_ref(sz);
        lean_panic_out_of_memory();
    }
    size_t n = lean_unbox(sz);
    object * r = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++) {
        lean_inc_ref(fn);
        lean_array_set_core(r, i, lean_apply_1(fn, lean_box(i)));
    }
    lean_dec_ref(fn);
    return r;
}

extern "C" lean_object * lean_array_data(lean_obj_arg a, lean_obj_arg i) {
    object * r = lean_array_fget(a, i);
    lean_dec(a);
    lean_dec(i);
    return r;
}

// =======================================
// Thunks

static obj_res mk_thunk_3_2(lean_cfun3 fn, obj_arg a1, obj_arg a2) {
    return lean_mk_thunk(mk_closure_3_2(fn, a1, a2));
}

extern "C" b_obj_res lean_thunk_get_core(b_obj_arg t) {
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

static obj_res thunk_map_fn_closure(obj_arg f, obj_arg t, obj_arg /* u */) {
    b_obj_res v = lean_thunk_get(t);
    lean_inc(v);
    obj_res r = lean_apply_1(f, v);
    lean_dec(v);
    return r;
}

extern "C" obj_res lean_thunk_map(obj_arg f, obj_arg t) {
    lean_assert(lean_is_closure(f));
    lean_assert(lean_is_thunk(t));
    return mk_thunk_3_2(thunk_map_fn_closure, f, t);
}

static obj_res thunk_bind_fn_closure(obj_arg x, obj_arg f, obj_arg /* u */) {
    b_obj_res v = lean_thunk_get(x);
    lean_inc(v);
    obj_res r = lean_apply_1(f, v);
    lean_dec(x);
    return r;
}

extern "C" obj_res lean_thunk_bind(obj_arg x, obj_arg f) {
    return mk_thunk_3_2(thunk_bind_fn_closure, x, f);
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

extern "C" obj_res lean_fixpoint(obj_arg rec, obj_arg a) {
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

extern "C" obj_res lean_fixpoint2(obj_arg rec, obj_arg a1, obj_arg a2) {
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

extern "C" obj_res lean_fixpoint3(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3) {
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

extern "C" obj_res lean_fixpoint4(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4) {
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

extern "C" obj_res lean_fixpoint5(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5) {
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

extern "C" obj_res lean_fixpoint6(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5, obj_arg a6) {
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

extern "C" void lean_mark_persistent(object * o) {
    buffer<object*> todo;
    todo.push_back(o);
    while (!todo.empty()) {
        object * o = todo.back();
        todo.pop_back();
        if (!lean_is_scalar(o) && lean_has_rc(o)) {
#if defined(LEAN_COMPRESSED_OBJECT_HEADER)
            o->m_header &= ~((1ull << LEAN_ST_BIT) | (1ull << LEAN_MT_BIT));
            o->m_header |=  (1ull << LEAN_PERSISTENT_BIT);
#elif defined(LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC)
            LEAN_BYTE(o->m_header, 5) = LEAN_PERSISTENT_MEM_KIND;
#else
            o->m_mem_kind = LEAN_PERSISTENT_MEM_KIND;
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

extern "C" void lean_mark_mt(object * o) {
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
#if defined(LEAN_COMPRESSED_OBJECT_HEADER)
            o->m_header &= ~(1ull << LEAN_ST_BIT);
            o->m_header |=  (1ull << LEAN_MT_BIT);
#elif defined(LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC)
            LEAN_BYTE(o->m_header, 5) = LEAN_MT_MEM_KIND;
#else
            o->m_mem_kind = LEAN_MT_MEM_KIND;
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

static lean_task_imp * alloc_task_imp(obj_arg c, unsigned prio) {
    lean_task_imp * imp = (lean_task_imp*)lean_alloc_small_object(sizeof(lean_task_imp));
    imp->m_closure     = c;
    imp->m_head_dep    = nullptr;
    imp->m_next_dep    = nullptr;
    imp->m_prio        = prio;
    imp->m_interrupted = false;
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
    struct worker_info {
        std::unique_ptr<lthread> m_thread;
        lean_task_object *       m_task;
    };
    typedef std::vector<worker_info *> workers;

    mutex                                         m_mutex;
    unsigned                                      m_workers_to_be_created;
    workers                                       m_workers;
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

    void enqueue_core(lean_task_object * t) {
        lean_assert(t->m_imp);
        unsigned prio = t->m_imp->m_prio;
        if (prio > LEAN_MAX_PRIO)
            prio = LEAN_MAX_PRIO;
        if (prio > m_max_prio)
            m_max_prio = prio;
        m_queues[prio].push_back(t);
        m_queues_size++;
        if (m_workers_to_be_created > 0)
            spawn_worker();
        else
            m_queue_cv.notify_one();
    }

    void spawn_worker() {
        lean_assert(m_workers_to_be_created > 0);
        worker_info * this_worker = new worker_info();
        m_workers.push_back(this_worker);
        m_workers_to_be_created--;
        this_worker->m_thread.reset(new lthread([this, this_worker]() {
                    save_stack_info(false);
                    unique_lock<mutex> lock(m_mutex);
                    while (true) {
                        if (m_shutting_down) {
                            break;
                        }

                        if (m_queues_size == 0) {
                            m_queue_cv.wait(lock);
                            continue;
                        }

                        lean_task_object * t = dequeue();
                        lean_assert(t->m_imp);
                        if (t->m_imp->m_deleted) {
                            free_task(t);
                            continue;
                        }
                        reset_heartbeat();
                        object * v = nullptr;
                        {
                            flet<lean_task_object *> update_task(this_worker->m_task, t);
                            scoped_current_task_object scope_cur_task(t);
                            object * c = t->m_imp->m_closure;
                            t->m_imp->m_closure = nullptr;
                            lock.unlock();
                            v = lean_apply_1(c, box(0));
                            lock.lock();
                        }
                        lean_assert(t->m_imp);
                        if (t->m_imp->m_deleted) {
                            if (v) lean_dec(v);
                            free_task(t);
                        } else if (v != nullptr) {
                            lean_assert(t->m_imp->m_closure == nullptr);
                            handle_finished(t);
                            t->m_value = v;
                            /* After the task has been finished and we propagated
                               dependecies, we can release `m_imp` and keep just the value */
                            free_task_imp(t->m_imp);
                            t->m_imp   = nullptr;
                            m_task_finished_cv.notify_all();
                        }
                        reset_heartbeat();
                    }
                    run_thread_finalizers();
                    run_post_thread_finalizers();
                }));
    }

    void handle_finished(lean_task_object * t) {
        lean_task_object * it = t->m_imp->m_head_dep;
        t->m_imp->m_head_dep = nullptr;
        while (it) {
            if (t->m_imp->m_interrupted)
                it->m_imp->m_interrupted = true;
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
            lean_assert(lean_is_thunk(head) || lean_is_task(head));
            if (lean_is_thunk(head) || lean_to_task(head)->m_value)
                return head;
            it = cnstr_get(it, 1);
        }
        return nullptr;
    }

public:
    task_manager(unsigned num_workers):
        m_workers_to_be_created(num_workers) {
    }

    ~task_manager() {
        unique_lock<mutex> lock(m_mutex);
        for (worker_info * info : m_workers) {
            if (info->m_task) {
                lean_assert(info->m_task->m_imp);
                info->m_task->m_imp->m_interrupted = true;
            }
        }
        m_shutting_down = true;
        m_queue_cv.notify_all();
        lock.unlock();
        for (worker_info * w : m_workers) {
            w->m_thread->join();
            delete w;
        }
        for (std::deque<lean_task_object *> const & q : m_queues) {
            for (lean_task_object * o : q) {
                lean_assert(o->m_imp && o->m_imp->m_deleted);
                free_task(o);
            }
        }
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
            object * c              = t->m_imp->m_closure;
            lean_task_object * it   = t->m_imp->m_head_dep;
            t->m_imp->m_closure     = nullptr;
            t->m_imp->m_head_dep    = nullptr;
            t->m_imp->m_interrupted = true;
            t->m_imp->m_deleted     = true;
            lock.unlock();
            while (it) {
                lean_assert(it->m_imp->m_deleted);
                lean_task_object * next_it = it->m_imp->m_next_dep;
                free_task(it);
                it = next_it;
            }
            if (c) dec_ref(c);
        }
    }

    void request_interrupt(lean_task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        if (t->m_imp)
            t->m_imp->m_interrupted = true;
    }
};

static task_manager * g_task_manager = nullptr;

extern "C" void lean_init_task_manager_using(unsigned num_workers) {
    lean_assert(g_task_manager == nullptr);
#if defined(LEAN_MULTI_THREAD)
    g_task_manager = new task_manager(num_workers);
#endif
}

extern "C" void lean_init_task_manager() {
    lean_init_task_manager_using(hardware_concurrency());
}

scoped_task_manager::scoped_task_manager(unsigned num_workers) {
    lean_assert(g_task_manager == nullptr);
#if defined(LEAN_MULTI_THREAD)
    g_task_manager = new task_manager(num_workers);
#endif
}

scoped_task_manager::~scoped_task_manager() {
    if (g_task_manager) {
        delete g_task_manager;
        g_task_manager = nullptr;
    }
}

void deactivate_task(lean_task_object * t) {
    lean_assert(g_task_manager);
    g_task_manager->deactivate_task(t);
}

static inline void lean_set_task_header(lean_object * o) {
#if defined(LEAN_COMPRESSED_OBJECT_HEADER)
    o->m_header   = ((size_t)(LeanTask) << 56) | (1ull << LEAN_MT_BIT) | 1;
#elif defined(LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC)
    o->m_header   = ((size_t)(LeanTask) << 56) | ((size_t)LEAN_MT_MEM_KIND << 40) | 1;
#else
    o->m_rc       = 1;
    o->m_tag      = LeanTask;
    o->m_mem_kind = LEAN_MT_MEM_KIND;
    o->m_other    = 0;
#endif
}

static lean_task_object * alloc_task(obj_arg c, unsigned prio) {
    lean_task_object * o = (lean_task_object*)lean_alloc_small_object(sizeof(lean_task_object));
    lean_set_task_header((lean_object*)o);
    o->m_value = nullptr;
    o->m_imp   = alloc_task_imp(c, prio);
    return o;
}

static lean_task_object * alloc_task(obj_arg v) {
    lean_task_object * o = (lean_task_object*)lean_alloc_small_object(sizeof(lean_task_object));
    lean_set_st_header((lean_object*)o, LeanTask, 0);
    o->m_value = v;
    o->m_imp   = nullptr;
    return o;
}


extern "C" obj_res lean_mk_task_with_prio(obj_arg c, unsigned prio) {
    if (!g_task_manager) {
        return lean_mk_thunk(c);
    } else {
        lean_task_object * new_task = alloc_task(c, prio);
        g_task_manager->enqueue(new_task);
        return (lean_object*)new_task;
    }
}

extern "C" obj_res lean_task_pure(obj_arg a) {
    if (!g_task_manager) {
        return lean_thunk_pure(a);
    } else {
        return (lean_object*)alloc_task(a);
    }
}

static obj_res task_map_fn(obj_arg f, obj_arg t, obj_arg) {
    lean_assert(lean_is_thunk(t) || lean_is_task(t));
    b_obj_res v;
    if (lean_is_thunk(t)) v = lean_thunk_get(t); else v = lean_to_task(t)->m_value;
    lean_assert(v != nullptr);
    lean_inc(v);
    lean_dec_ref(t);
    return lean_apply_1(f, v);
}

extern "C" obj_res lean_task_map_with_prio(obj_arg f, obj_arg t, unsigned prio) {
    if (!g_task_manager) {
        lean_assert(lean_is_thunk(t));
        return lean_thunk_map(f, t);
    } else {
        lean_task_object * new_task = alloc_task(mk_closure_3_2(task_map_fn, f, t), prio);
        if (lean_is_thunk(t))
            g_task_manager->enqueue(new_task);
        else
            g_task_manager->add_dep(lean_to_task(t), new_task);
        return (lean_object*)new_task;
    }
}

extern "C" b_obj_res lean_task_get(b_obj_arg t) {
    if (lean_is_thunk(t)) {
        return lean_thunk_get(t);
    } else {
        if (object * v = lean_to_task(t)->m_value)
            return v;
        g_task_manager->wait_for(lean_to_task(t));
        lean_assert(lean_to_task(t)->m_value != nullptr);
        object * r = lean_to_task(t)->m_value;
        return r;
    }
}

static obj_res task_bind_fn2(obj_arg t, obj_arg) {
    lean_assert(lean_to_task(t)->m_value);
    b_obj_res v = lean_to_task(t)->m_value;
    lean_inc(v);
    lean_dec_ref(t);
    return v;
}

static obj_res task_bind_fn1(obj_arg x, obj_arg f, obj_arg) {
    lean_assert(lean_is_thunk(x) || lean_is_task(x));
    b_obj_res v;
    if (lean_is_thunk(x)) v = lean_thunk_get(x); else v = lean_to_task(x)->m_value;
    lean_assert(v != nullptr);
    lean_inc(v);
    lean_dec_ref(x);
    obj_res new_task = lean_apply_1(f, v);
    lean_assert(lean_is_thunk(new_task) || lean_is_task(new_task));
    if (lean_is_thunk(new_task)) {
        b_obj_res r = lean_thunk_get(new_task);
        lean_inc(r);
        lean_dec_ref(new_task);
        return r;
    } else {
        lean_assert(lean_is_task(new_task));
        lean_assert(g_current_task_object->m_imp);
        lean_assert(g_current_task_object->m_imp->m_closure == nullptr);
        g_current_task_object->m_imp->m_closure = mk_closure_2_1(task_bind_fn2, new_task);
        g_task_manager->add_dep(lean_to_task(new_task), g_current_task_object);
        return nullptr; /* notify queue that task did not finish yet. */
    }
}

extern "C" obj_res lean_task_bind_with_prio(obj_arg x, obj_arg f, unsigned prio) {
    lean_assert(lean_is_thunk(x) || lean_is_task(x));
    if (!g_task_manager) {
        return lean_thunk_bind(x, f);
    } else {
        lean_task_object * new_task = alloc_task(mk_closure_3_2(task_bind_fn1, x, f), prio);
        if (lean_is_thunk(x))
            g_task_manager->enqueue(new_task);
        else
            g_task_manager->add_dep(lean_to_task(x), new_task);
        return (lean_object*)new_task;
    }
}

extern "C" bool lean_io_check_interrupt_core() {
    if (lean_task_object * t = g_current_task_object) {
        lean_assert(t->m_imp); // task is being executed
        return t->m_imp->m_interrupted;
    }
    return false;
}

extern "C" void lean_io_request_interrupt_core(b_obj_arg t) {
    lean_assert(lean_is_thunk(t) || lean_is_task(t));
    if (lean_is_thunk(t) || lean_to_task(t)->m_value)
        return;
    g_task_manager->request_interrupt(lean_to_task(t));
}

extern "C" bool lean_io_has_finished_core(b_obj_arg t) {
    lean_assert(lean_is_thunk(t) || lean_is_task(t));
    return lean_is_thunk(t) || lean_to_task(t)->m_value != nullptr;
}

extern "C" b_obj_res lean_io_wait_any_core(b_obj_arg task_list) {
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

object * mpz_to_nat_core(mpz const & m) {
    lean_assert(m > LEAN_MAX_SMALL_NAT);
    return alloc_mpz(m);
}

static inline obj_res mpz_to_nat(mpz const & m) {
    if (m.is_size_t() && m.get_size_t() <= LEAN_MAX_SMALL_NAT)
        return lean_box(m.get_size_t());
    else
        return mpz_to_nat_core(m);
}

extern "C" object * lean_cstr_to_nat(char const * n) {
    return mpz_to_nat(mpz(n));
}

extern "C" object * lean_big_usize_to_nat(size_t n) {
    if (n <= LEAN_MAX_SMALL_NAT) {
        return lean_box(n);
    } else {
        return mpz_to_nat_core(mpz::of_size_t(n));
    }
}

extern "C" object * lean_big_uint64_to_nat(uint64_t n) {
    if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT)) {
        return lean_box(n);
    } else {
        return mpz_to_nat_core(mpz(n));
    }
}

extern "C" object * lean_nat_big_succ(object * a) {
    return mpz_to_nat_core(mpz_value(a) + 1);
}

extern "C" object * lean_nat_big_add(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat_core(mpz::of_size_t(lean_unbox(a1)) + mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat_core(mpz_value(a1) + mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat_core(mpz_value(a1) + mpz_value(a2));
}

extern "C" object * lean_nat_big_sub(object * a1, object * a2) {
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

extern "C" object * lean_nat_big_mul(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat_core(mpz::of_size_t(lean_unbox(a1)) * mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat_core(mpz_value(a1) * mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat_core(mpz_value(a1) * mpz_value(a2));
}

extern "C" object * lean_nat_overflow_mul(size_t a1, size_t a2) {
    return mpz_to_nat_core(mpz::of_size_t(a1) * mpz::of_size_t(a2));
}

extern "C" object * lean_nat_big_div(object * a1, object * a2) {
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

extern "C" object * lean_nat_big_mod(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        return a1;
    } else if (lean_is_scalar(a2)) {
        usize n2 = lean_unbox(a2);
        return n2 == 0 ? a2 : lean_box((mpz_value(a1) % mpz::of_size_t(n2)).get_unsigned_int());
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mpz_to_nat(mpz_value(a1) % mpz_value(a2));
    }
}

extern "C" bool lean_nat_big_eq(object * a1, object * a2) {
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

extern "C" bool lean_nat_big_le(object * a1, object * a2) {
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

extern "C" bool lean_nat_big_lt(object * a1, object * a2) {
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

extern "C" object * lean_nat_big_land(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) & mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat(mpz_value(a1) & mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat(mpz_value(a1) & mpz_value(a2));
}

extern "C" object * lean_nat_big_lor(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) | mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat(mpz_value(a1) | mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat(mpz_value(a1) | mpz_value(a2));
}

extern "C" object * lean_nat_big_lxor(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) ^ mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_nat(mpz_value(a1) ^ mpz::of_size_t(lean_unbox(a2)));
    else
        return mpz_to_nat(mpz_value(a1) ^ mpz_value(a2));
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

extern "C" object * lean_cstr_to_int(char const * n) {
    return mpz_to_int(mpz(n));
}

extern "C" object * lean_big_int_to_int(int n) {
    return alloc_mpz(mpz(n));
}

extern "C" object * lean_big_size_t_to_int(size_t n) {
    return alloc_mpz(mpz::of_size_t(n));
}

extern "C" object * lean_big_int64_to_int(int64_t n) {
    if (LEAN_LIKELY(LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT)) {
        return lean_box(static_cast<unsigned>(static_cast<int>(n)));
    } else {
        return mpz_to_int_core(mpz(n));
    }
}

extern "C" object * lean_int_big_neg(object * a) {
    return mpz_to_int(neg(mpz_value(a)));
}

extern "C" object * lean_int_big_add(object * a1, object * a2) {
    if (lean_is_scalar(a1))
        return mpz_to_int(lean_scalar_to_int(a1) + mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_int(mpz_value(a1) + lean_scalar_to_int(a2));
    else
        return mpz_to_int(mpz_value(a1) + mpz_value(a2));
}

extern "C" object * lean_int_big_sub(object * a1, object * a2) {
    if (lean_is_scalar(a1))
        return mpz_to_int(lean_scalar_to_int(a1) - mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_int(mpz_value(a1) - lean_scalar_to_int(a2));
    else
        return mpz_to_int(mpz_value(a1) - mpz_value(a2));
}

extern "C" object * lean_int_big_mul(object * a1, object * a2) {
    if (lean_is_scalar(a1))
        return mpz_to_int(lean_scalar_to_int(a1) * mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_int(mpz_value(a1) * lean_scalar_to_int(a2));
    else
        return mpz_to_int(mpz_value(a1) * mpz_value(a2));
}

extern "C" object * lean_int_big_div(object * a1, object * a2) {
    if (lean_is_scalar(a1))
        return mpz_to_int(lean_scalar_to_int(a1) / mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_int(mpz_value(a1) / lean_scalar_to_int(a2));
    else
        return mpz_to_int(mpz_value(a1) / mpz_value(a2));
}

extern "C" object * lean_int_big_mod(object * a1, object * a2) {
    if (lean_is_scalar(a1))
        return mpz_to_int(mpz(lean_scalar_to_int(a1)) % mpz_value(a2));
    else if (lean_is_scalar(a2))
        return mpz_to_int(mpz_value(a1) % mpz(lean_scalar_to_int(a2)));
    else
        return mpz_to_int(mpz_value(a1) % mpz_value(a2));
}

extern "C" bool lean_int_big_eq(object * a1, object * a2) {
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

extern "C" bool lean_int_big_le(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        return lean_scalar_to_int(a1) <= mpz_value(a2);
    } else if (lean_is_scalar(a2)) {
        return mpz_value(a1) <= lean_scalar_to_int(a2);
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

extern "C" bool lean_int_big_lt(object * a1, object * a2) {
    if (lean_is_scalar(a1)) {
        return lean_scalar_to_int(a1) < mpz_value(a2);
    } else if (lean_is_scalar(a2)) {
        return mpz_value(a1) < lean_scalar_to_int(a2);
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

extern "C" bool lean_int_big_nonneg(object * a) {
    return mpz_value(a) >= 0;
}

// =======================================
// UInt

extern "C" uint8 lean_uint8_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 8);
    return static_cast<uint8>(r.get_unsigned_int());
}

extern "C" uint16 lean_uint16_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 16);
    return static_cast<uint16>(r.get_unsigned_int());
}

extern "C" uint32 lean_uint32_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 32);
    return static_cast<uint32>(r.get_unsigned_int());
}

extern "C" uint32 lean_uint32_big_modn(uint32 a1, b_lean_obj_arg a2) {
    mpz const & m = mpz_value(a2);
    return m.is_unsigned_int() ? a1 % m.get_unsigned_int() : a1;
}

extern "C" uint64 lean_uint64_of_big_nat(b_obj_arg a) {
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

extern "C" uint64 lean_uint64_big_modn(uint64 a1, b_lean_obj_arg) {
    // TODO(Leo)
    return a1;
}

extern "C" usize lean_usize_of_big_nat(b_obj_arg a) {
    return mpz_value(a).get_size_t();
}

extern "C" usize lean_usize_big_modn(usize a1, b_lean_obj_arg) {
    // TODO(Leo)
    return a1;
}

extern "C" usize lean_usize_mix_hash(usize a1, usize a2) {
    if (sizeof(void*) == 8)
        return hash(static_cast<uint64>(a1), static_cast<uint64>(a2));
    else
        return hash(static_cast<uint32>(a1), static_cast<uint32>(a2));
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

extern "C" object * lean_mk_string(char const * s) {
    size_t sz  = strlen(s);
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = lean_alloc_string(rsz, rsz, len);
    memcpy(w_string_cstr(r), s, sz+1);
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

extern "C" object * lean_string_push(object * s, unsigned c) {
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

extern "C" object * lean_string_append(object * s1, object * s2) {
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

extern "C" bool lean_string_lt(object * s1, object * s2) {
    size_t sz1 = lean_string_size(s1) - 1; // ignore null char in the end
    size_t sz2 = lean_string_size(s2) - 1; // ignore null char in the end
    int r      = std::memcmp(lean_string_cstr(s1), lean_string_cstr(s2), std::min(sz1, sz2));
    return r < 0 || (r == 0 && sz1 < sz2);
}

static std::string list_as_string(b_obj_arg lst) {
    std::string s;
    b_obj_arg o = lst;
    while (!lean_is_scalar(o)) {
        push_unicode_scalar(s, lean_unbox(lean_ctor_get(o, 0)));
        o = lean_ctor_get(o, 1);
    }
    return s;
}

static obj_res string_to_list_core(std::string const & s, bool reverse = false) {
    buffer<unsigned> tmp;
    utf8_decode(s, tmp);
    if (reverse)
        std::reverse(tmp.begin(), tmp.end());
    obj_res  r = lean_box(0);
    unsigned i = tmp.size();
    while (i > 0) {
        --i;
        obj_res new_r = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(new_r, 0, lean_box(tmp[i]));
        lean_ctor_set(new_r, 1, r);
        r = new_r;
    }
    return r;
}

extern "C" obj_res lean_string_mk(obj_arg cs) {
    std::string s = list_as_string(cs);
    lean_dec(cs);
    return mk_string(s);
}

extern "C" obj_res lean_string_data(obj_arg s) {
    std::string tmp = string_to_std(s);
    lean_dec_ref(s);
    return string_to_list_core(tmp);
}

extern "C" uint32 lean_string_utf8_get(b_obj_arg s, b_obj_arg i0) {
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
extern "C" obj_res lean_string_utf8_next(b_obj_arg s, b_obj_arg i0) {
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

extern "C" obj_res lean_string_utf8_extract(b_obj_arg s, b_obj_arg b0, b_obj_arg e0) {
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

extern "C" obj_res lean_string_utf8_prev(b_obj_arg s, b_obj_arg i0) {
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

extern "C" obj_res lean_string_utf8_set(obj_arg s, b_obj_arg i0, uint32 c) {
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
    new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
    return mk_string(new_s);
}

extern "C" usize lean_string_hash(b_obj_arg s) {
    usize sz = lean_string_size(s) - 1;
    char const * str = lean_string_cstr(s);
    return hash_str(sz, str, 11);
}

// =======================================
// ByteArray

extern "C" obj_res lean_copy_sarray(obj_arg a, bool expand) {
    unsigned esz   = lean_sarray_elem_size(a);
    size_t sz      = lean_sarray_size(a);
    size_t cap     = lean_sarray_capacity(a);
    lean_assert(cap >= sz);
    if (expand) cap = (cap + 1) * 2;
    lean_assert(!expand || cap > sz);
    object * r     = lean_alloc_sarray(esz, sz, cap);
    uint8 * it     = lean_sarray_cptr(a);
    uint8 * dest   = lean_sarray_cptr(r);
    memcpy(dest, it, esz*sz);
    lean_dec(a);
    return r;
}

extern "C" obj_res lean_copy_byte_array(obj_arg a) {
    return lean_copy_sarray(a, false);
}

extern "C" obj_res lean_byte_array_mk(obj_arg a) {
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

extern "C" obj_res lean_byte_array_data(obj_arg a) {
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

extern "C" obj_res lean_byte_array_push(obj_arg a, uint8 b) {
    object * r;
    if (lean_is_exclusive(a)) {
        if (lean_sarray_capacity(a) > lean_sarray_size(a))
            r = a;
        else
            r = lean_copy_sarray(a, true);
    } else {
        r = lean_copy_sarray(a, lean_sarray_capacity(a) < 2*lean_sarray_size(a) + 1);
    }
    lean_assert(lean_sarray_capacity(r) > lean_sarray_size(r));
    size_t & sz  = lean_to_sarray(r)->m_size;
    uint8 * it   = lean_sarray_cptr(r) + sz;
    *it = b;
    sz++;
    return r;
}

// =======================================
// Array functions for generated code

extern "C" object * lean_mk_array(obj_arg n, obj_arg v) {
    size_t sz;
    if (lean_is_scalar(n)) {
        sz = lean_unbox(n);
    } else {
        mpz const & v = mpz_value(n);
        if (!v.is_size_t()) lean_panic_out_of_memory();
        sz = v.get_size_t();
        lean_dec(n);
    }
    object * r    = lean_alloc_array(sz, sz);
    object ** it  = lean_array_cptr(r);
    object ** end = it + sz;
    for (; it != end; ++it) {
        *it = v;
    }
    if (sz > 1) lean_inc_n(v, sz - 1);
    return r;
}

extern "C" obj_res lean_copy_expand_array(obj_arg a, bool expand) {
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

extern "C" object * lean_array_push(obj_arg a, obj_arg v) {
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
// Runtime info

extern "C" object * lean_closure_max_args(object *) {
    return lean_unsigned_to_nat((unsigned)LEAN_CLOSURE_MAX_ARGS);
}

extern "C" object * lean_max_small_nat(object *) {
    return lean_usize_to_nat(LEAN_MAX_SMALL_NAT);
}

// =======================================
// Debugging helper functions

void dbg_print_str(object * o) {
    lean_assert(is_string(o));
    std::cout << string_cstr(o) << "\n";
}

void dbg_print_num(object * o) {
    if (is_scalar(o)) {
        std::cout << unbox(o) << "\n";
    } else {
        std::cout << mpz_value(o) << "\n";
    }
}

static mutex g_dbg_mutex;

extern "C" object * lean_dbg_trace(obj_arg s, obj_arg fn) {
    {
        unique_lock<mutex> lock(g_dbg_mutex);
        std::cout << lean_string_cstr(s) << std::endl;
    }
    lean_dec(s);
    return lean_apply_1(fn, lean_box(0));
}

extern "C" object * lean_dbg_sleep(uint32 ms, obj_arg fn) {
    chrono::milliseconds c(ms);
    this_thread::sleep_for(c);
    return lean_apply_1(fn, lean_box(0));
}

extern "C" object * lean_dbg_trace_if_shared(obj_arg s, obj_arg a) {
    if (lean_is_shared(a)) {
        unique_lock<mutex> lock(g_dbg_mutex);
        std::cout << "shared RC " << lean_string_cstr(s) << std::endl;
    }
    lean_dec(s);
    return a;
}

// =======================================
// Module initialization

static std::vector<lean_external_class*> * g_ext_classes;
static mutex                             * g_ext_classes_mutex;

extern "C" lean_external_class * lean_register_external_class(lean_external_finalize_proc p1, lean_external_foreach_proc p2) {
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

extern "C" void lean_dbg_print_str(lean::object* o) { lean::dbg_print_str(o); }
extern "C" void lean_dbg_print_num(lean::object* o) { lean::dbg_print_num(o); }
