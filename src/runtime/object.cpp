/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <iostream>
#include <string>
#include <algorithm>
#include <map>
#include <vector>
#include <utility>
#include <unordered_set>
#include <deque>
#include "runtime/stackinfo.h"
#include "runtime/object.h"
#include "runtime/utf8.h"
#include "runtime/apply.h"
#include "runtime/flet.h"
#include "runtime/interrupt.h"
#include "runtime/hash.h"
#include "runtime/alloc.h"

#define LEAN_MAX_PRIO 8

namespace lean {
// =======================================
// External objects

struct external_object_class {
    external_object_finalize_proc m_finalize;
    external_object_foreach_proc  m_foreach;
};

static std::vector<external_object_class*> * g_ext_classes;
static mutex                               * g_ext_classes_mutex;

external_object_class * register_external_object_class(external_object_finalize_proc p1, external_object_foreach_proc p2) {
    unique_lock<mutex> lock(*g_ext_classes_mutex);
    external_object_class * cls = new external_object_class{p1, p2};
    g_ext_classes->push_back(cls);
    return cls;
}

// =======================================
// Object

size_t obj_byte_size(object * o) {
    switch (get_kind(o)) {
    case object_kind::Constructor:     return cnstr_byte_size(o);
    case object_kind::Closure:         return closure_byte_size(o);
    case object_kind::Array:           return array_byte_size(o);
    case object_kind::ScalarArray:     return sarray_byte_size(o);
    case object_kind::String:          return string_byte_size(o);
    case object_kind::MPZ:             return sizeof(mpz_object);
    case object_kind::Thunk:           return sizeof(thunk_object);
    case object_kind::Task:            return sizeof(task_object);
    case object_kind::Ref:             return sizeof(ref_object);
    case object_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

size_t obj_header_size(object * o) {
    switch (get_kind(o)) {
    case object_kind::Constructor:     return sizeof(constructor_object);
    case object_kind::Closure:         return sizeof(closure_object);
    case object_kind::Array:           return sizeof(array_object);
    case object_kind::ScalarArray:     return sizeof(sarray_object);
    case object_kind::String:          return sizeof(string_object);
    case object_kind::MPZ:             return sizeof(mpz_object);
    case object_kind::Thunk:           return sizeof(thunk_object);
    case object_kind::Task:            return sizeof(task_object);
    case object_kind::Ref:             return sizeof(ref_object);
    case object_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

/* We use the RC memory to implement a linked list of lean objects to be deleted.
   This hack is safe because rc_type is uintptr_t. */

static_assert(sizeof(atomic<rc_type>) == sizeof(object*),  "unexpected atomic<rc_type> size, the object GC assumes these two types have the same size"); // NOLINT

#ifdef LEAN_LAZY_RC
LEAN_THREAD_PTR(object, g_to_free);
#endif

inline object * get_next(object * o) {
    return *reinterpret_cast<object**>(st_rc_addr(o));
}

inline void set_next(object * o, object * n) {
    *reinterpret_cast<object**>(st_rc_addr(o)) = n;
}

inline void push_back(object * & todo, object * v) {
    set_next(v, todo);
    todo = v;
}

inline object * pop_back(object * & todo) {
    object * r = todo;
    todo = get_next(todo);
    return r;
}

inline void dec_ref(object * o, object* & todo) {
    if (dec_ref_core(o))
        push_back(todo, o);
}

inline void dec(object * o, object* & todo) {
    if (!is_scalar(o) && dec_ref_core(o))
        push_back(todo, o);
}

void deactivate_task(task_object * t);

#ifdef LEAN_SMALL_ALLOCATOR
static inline void free_heap_obj_core(object * o, size_t sz) {
#else
static inline void free_heap_obj_core(object * o) {
#endif
#ifdef LEAN_FAKE_FREE
    // Set kinds to invalid values, which should trap any further accesses in debug mode.
    // Make sure object kind is recoverable for printing deleted objects
    if (o->m_mem_kind != 42) {
        o->m_kind = -o->m_kind;
        o->m_mem_kind = 42;
    }
#else
#ifdef LEAN_SMALL_ALLOCATOR
    dealloc(reinterpret_cast<char *>(o) - sizeof(rc_type), sz);
#else
    free(reinterpret_cast<char *>(o) - sizeof(rc_type));
#endif
#endif
}

#ifdef LEAN_SMALL_ALLOCATOR
#define FREE_OBJ(o, sz) free_heap_obj_core(o, sz)
#else
#define FREE_OBJ(o, sz) free_heap_obj_core(o)
#endif

void free_heap_obj(object * o) {
    FREE_OBJ(o, obj_byte_size(o) + sizeof(rc_type));
}

static inline void free_cnstr_obj(object * o) {
    FREE_OBJ(o, cnstr_byte_size(o) + sizeof(rc_type));
}

static inline void free_closure_obj_core(object * o) {
    FREE_OBJ(o, closure_byte_size(o) + sizeof(rc_type));
}

void free_closure_obj(object * o) {
    return free_closure_obj_core(o);
}

static inline void free_array_obj(object * o) {
    FREE_OBJ(o, array_byte_size(o) + sizeof(rc_type));
}

static inline void free_sarray_obj(object * o) {
    FREE_OBJ(o, sarray_byte_size(o) + sizeof(rc_type));
}

static inline void free_string_obj(object * o) {
    FREE_OBJ(o, string_byte_size(o) + sizeof(rc_type));
}

inline void free_mpz_obj(object * o) {
    FREE_OBJ(o, sizeof(mpz_object) + sizeof(rc_type));
}

static inline void free_thunk_obj(object * o) {
    FREE_OBJ(o, sizeof(thunk_object) + sizeof(rc_type));
}

static inline void free_ref_obj(object * o) {
    FREE_OBJ(o, sizeof(ref_object) + sizeof(rc_type));
}

static inline void free_task_obj(object * o) {
    FREE_OBJ(o, sizeof(task_object) + sizeof(rc_type));
}

static inline void free_external_obj(object * o) {
    FREE_OBJ(o, sizeof(external_object) + sizeof(rc_type));
}

static void del_core(object * o, object * & todo) {
    lean_assert(is_heap_obj(o));
    LEAN_RUNTIME_STAT_CODE(g_num_del++);
    switch (get_kind(o)) {
    case object_kind::Constructor: {
        object ** it  = cnstr_obj_cptr(o);
        object ** end = it + cnstr_num_objs(o);
        for (; it != end; ++it) dec(*it, todo);
        free_cnstr_obj(o);
        break;
    }
    case object_kind::Closure: {
        object ** it  = closure_arg_cptr(o);
        object ** end = it + closure_num_fixed(o);
        for (; it != end; ++it) dec(*it, todo);
        free_closure_obj_core(o);
        break;
    }
    case object_kind::Array: {
        object ** it  = array_cptr(o);
        object ** end = it + array_size(o);
        for (; it != end; ++it) dec(*it, todo);
        free_array_obj(o);
        break;
    }
    case object_kind::ScalarArray:
        free_sarray_obj(o); break;
    case object_kind::String:
        free_string_obj(o); break;
    case object_kind::MPZ:
        dealloc_mpz(o); break;
    case object_kind::Thunk:
        if (object * c = to_thunk(o)->m_closure) dec(c, todo);
        if (object * v = to_thunk(o)->m_value) dec(v, todo);
        free_thunk_obj(o);
        break;
    case object_kind::Ref:
        if (object * v = to_ref(o)->m_value) dec(v, todo);
        free_ref_obj(o);
        break;
    case object_kind::Task:
        deactivate_task(to_task(o));
        break;
    case object_kind::External:
        to_external(o)->m_class->m_finalize(to_external(o)->m_data);
        free_external_obj(o);
        break;
    }
}

void del(object * o) {
#ifdef LEAN_LAZY_RC
    push_back(g_to_free, o);
#else
    object * todo = nullptr;
    while (true) {
        lean_assert(is_heap_obj(o));
        del_core(o, todo);
        if (todo == nullptr)
            return;
        o = pop_back(todo);
    }
#endif
}

void * alloc_heap_object(size_t sz) {
#ifdef LEAN_LAZY_RC
    if (g_to_free) {
        object * o = pop_back(g_to_free);
        del_core(o, g_to_free);
    }
#endif
#ifdef LEAN_SMALL_ALLOCATOR
    void * r = alloc(sizeof(rc_type) + sz);
#else
    void * r = malloc(sizeof(rc_type) + sz);
    if (r == nullptr) throw std::bad_alloc();
#endif
    *static_cast<rc_type *>(r) = 1;
    return static_cast<char *>(r) + sizeof(rc_type);
}

// =======================================
// Arrays
static object * g_array_empty = nullptr;

object * array_mk_empty() {
    return g_array_empty;
}

// =======================================
// Closures

typedef object * (*lean_cfun2)(object *, object *); // NOLINT
typedef object * (*lean_cfun3)(object *, object *, object *); // NOLINT

static obj_res mk_closure_2_1(lean_cfun2 fn, obj_arg a) {
    object * c = alloc_closure(fn, 1);
    closure_set(c, 0, a);
    return c;
}

static obj_res mk_closure_3_2(lean_cfun3 fn, obj_arg a1, obj_arg a2) {
    object * c = alloc_closure(fn, 2);
    closure_set(c, 0, a1);
    closure_set(c, 1, a2);
    return c;
}

// =======================================
// Thunks

static obj_res mk_thunk_3_2(lean_cfun3 fn, obj_arg a1, obj_arg a2) {
    return mk_thunk(mk_closure_3_2(fn, a1, a2));
}

b_obj_res thunk_get_core(b_obj_arg t) {
    object * c = to_thunk(t)->m_closure.exchange(nullptr);
    if (c != nullptr) {
        /* Recall that a closure uses the standard calling convention.
           `thunk_get` "consumes" the result `r` by storing it at `to_thunk(t)->m_value`.
           Then, it returns a reference to this result to the caller.
           The behavior is compatible with `cnstr_obj` with also returns a reference
           to be object stored in the constructor object.

           Recall that `apply_1` also consumes `c`'s RC. */
        object * r = apply_1(c, box(0));
        lean_assert(r != nullptr); /* Closure must return a valid lean object */
        lean_assert(to_thunk(t)->m_value == nullptr);
        to_thunk(t)->m_value = r;
        return r;
    } else {
        lean_assert(c == nullptr);
        /* There is another thread executing the closure. We keep waiting for the m_value to be
           set by another thread. */
        while (!to_thunk(t)->m_value) {
            this_thread::yield();
        }
        return to_thunk(t)->m_value;
    }
}

static obj_res thunk_map_fn_closure(obj_arg f, obj_arg t, obj_arg /* u */) {
    b_obj_res v = thunk_get(t);
    inc(v);
    obj_res r = apply_1(f, v);
    dec(v);
    return r;
}

obj_res thunk_map(obj_arg f, obj_arg t) {
    lean_assert(is_closure(f));
    lean_assert(is_thunk(t));
    return mk_thunk_3_2(thunk_map_fn_closure, f, t);
}

static obj_res thunk_bind_fn_closure(obj_arg x, obj_arg f, obj_arg /* u */) {
    b_obj_res v = thunk_get(x);
    inc(v);
    obj_res r = apply_1(f, v);
    dec(x);
    return r;
}

obj_res thunk_bind(obj_arg x, obj_arg f) {
    return mk_thunk_3_2(thunk_bind_fn_closure, x, f);
}

// =======================================
// Tasks

LEAN_THREAD_PTR(task_object, g_current_task_object);

void dealloc_task(task_object * t) {
    if (t->m_imp) delete t->m_imp;
    free_task_obj(t);
}

struct scoped_current_task_object : flet<task_object *> {
    scoped_current_task_object(task_object * t):flet(g_current_task_object, t) {}
};

class task_manager {
    struct worker_info {
        std::unique_ptr<lthread> m_thread;
        task_object *            m_task;
    };
    typedef std::vector<worker_info *> workers;

    mutex                                         m_mutex;
    unsigned                                      m_workers_to_be_created;
    workers                                       m_workers;
    std::deque<task_object *>                     m_queues[LEAN_MAX_PRIO+1];
    unsigned                                      m_queues_size{0};
    unsigned                                      m_max_prio{0};
    condition_variable                            m_queue_cv;
    condition_variable                            m_task_finished_cv;
    bool                                          m_shutting_down{false};

    task_object * dequeue() {
        lean_assert(m_queues_size != 0);
        std::deque<task_object *> & q = m_queues[m_max_prio];
        lean_assert(!q.empty());
        task_object * result      = q.front();
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

    void enqueue_core(task_object * t) {
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

                        task_object * t = dequeue();
                        lean_assert(t->m_imp);
                        if (t->m_imp->m_deleted) {
                            dealloc_task(t);
                            continue;
                        }
                        reset_heartbeat();
                        object * v = nullptr;
                        {
                            flet<task_object *> update_task(this_worker->m_task, t);
                            scoped_current_task_object scope_cur_task(t);
                            object * c = t->m_imp->m_closure;
                            t->m_imp->m_closure = nullptr;
                            lock.unlock();
                            v = apply_1(c, box(0));
                            lock.lock();
                        }
                        lean_assert(t->m_imp);
                        if (t->m_imp->m_deleted) {
                            if (v) dec(v);
                            dealloc_task(t);
                        } else if (v != nullptr) {
                            lean_assert(t->m_imp->m_closure == nullptr);
                            handle_finished(t);
                            t->m_value = v;
                            /* After the task has been finished and we propagated
                               dependecies, we can release `m_imp` and keep just the value */
                            delete t->m_imp;
                            t->m_imp   = nullptr;
                            m_task_finished_cv.notify_all();
                        }
                        reset_heartbeat();
                    }

                    run_thread_finalizers();
                    run_post_thread_finalizers();
                }));
    }

    void handle_finished(task_object * t) {
        task_object * it = t->m_imp->m_head_dep;
        t->m_imp->m_head_dep = nullptr;
        while (it) {
            if (t->m_imp->m_interrupted)
                it->m_imp->m_interrupted = true;
            task_object * next_it = it->m_imp->m_next_dep;
            it->m_imp->m_next_dep = nullptr;
            if (it->m_imp->m_deleted) {
                dealloc_task(it);
            } else {
                enqueue_core(it);
            }
            it = next_it;
        }
    }

    object * wait_any_check(object * task_list) {
        object * it = task_list;
        while (!is_scalar(it)) {
            object * head = cnstr_get(it, 0);
            lean_assert(is_thunk(head) || is_task(head));
            if (is_thunk(head) || to_task(head)->m_value)
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
        for (std::deque<task_object *> const & q : m_queues) {
            for (task_object * o : q) {
                lean_assert(o->m_imp && o->m_imp->m_deleted);
                dealloc_task(o);
            }
        }
    }

    void enqueue(task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        enqueue_core(t);
    }

    void add_dep(task_object * t1, task_object * t2) {
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

    void wait_for(task_object * t) {
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

    void deactivate_task(task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        if (object * v = t->m_value) {
            lean_assert(t->m_imp == nullptr);
            lock.unlock();
            dec(v);
            free_task_obj(t);
            return;
        } else {
            lean_assert(t->m_imp);
            object * c       = t->m_imp->m_closure;
            task_object * it = t->m_imp->m_head_dep;
            t->m_imp->m_closure     = nullptr;
            t->m_imp->m_head_dep    = nullptr;
            t->m_imp->m_interrupted = true;
            t->m_imp->m_deleted     = true;
            lock.unlock();
            while (it) {
                lean_assert(it->m_imp->m_deleted);
                task_object * next_it = it->m_imp->m_next_dep;
                dealloc_task(it);
                it = next_it;
            }
            if (c) dec_ref(c);
        }
    }

    void request_interrupt(task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        if (t->m_imp)
            t->m_imp->m_interrupted = true;
    }
};

static task_manager * g_task_manager = nullptr;

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

void deactivate_task(task_object * t) {
    lean_assert(g_task_manager);
    g_task_manager->deactivate_task(t);
}

void mark_mt(object * o);
static obj_res mark_mt_fn(obj_arg o) {
    mark_mt(o);
    dec(o);
    return box(0);
}

void mark_mt(object * o) {
#ifndef LEAN_MULTI_THREAD
    return;
#endif
    if (is_scalar(o) || !is_st_heap_obj(o)) return;
    o->m_mem_kind = static_cast<unsigned>(object_memory_kind::MTHeap);

    switch (get_kind(o)) {
    case object_kind::ScalarArray:
    case object_kind::String:
    case object_kind::MPZ:
        return;
    case object_kind::External: {
        object * fn = alloc_closure(reinterpret_cast<void*>(mark_mt_fn), 1, 0);
        to_external(o)->m_class->m_foreach(to_external(o)->m_data, fn);
        dec(fn);
        return;
    }
    case object_kind::Task:
        mark_mt(task_get(o));
        return;
    case object_kind::Constructor: {
        object ** it  = cnstr_obj_cptr(o);
        object ** end = it + cnstr_num_objs(o);
        for (; it != end; ++it) mark_mt(*it);
        return;
    }
    case object_kind::Closure: {
        object ** it  = closure_arg_cptr(o);
        object ** end = it + closure_num_fixed(o);
        for (; it != end; ++it) mark_mt(*it);
        return;
    }
    case object_kind::Array: {
        object ** it  = array_cptr(o);
        object ** end = it + array_size(o);
        for (; it != end; ++it) mark_mt(*it);
        return;
    }
    case object_kind::Thunk:
        if (object * c = to_thunk(o)->m_closure) mark_mt(c);
        if (object * v = to_thunk(o)->m_value) mark_mt(v);
        return;
    case object_kind::Ref:
        if (object * v = to_ref(o)->m_value) mark_mt(v);
        return;
    }
}

task_object::task_object(obj_arg c, unsigned prio):
    object(object_kind::Task, object_memory_kind::MTHeap), m_value(nullptr), m_imp(new imp(c, prio)) {
    lean_assert(is_closure(c));
    mark_mt(c);
}

task_object::task_object(obj_arg v):
    object(object_kind::Task, object_memory_kind::STHeap), m_value(v), m_imp(nullptr) {
}

static task_object * alloc_task(obj_arg c, unsigned prio) {
    LEAN_RUNTIME_STAT_CODE(g_num_task++);
    return new (alloc_heap_object(sizeof(task_object))) task_object(c, prio); // NOLINT
}

static task_object * alloc_task(obj_arg v) {
    LEAN_RUNTIME_STAT_CODE(g_num_task++);
    return new (alloc_heap_object(sizeof(task_object))) task_object(v); // NOLINT
}

obj_res mk_task(obj_arg c, unsigned prio) {
    if (!g_task_manager) {
        return mk_thunk(c);
    } else {
        task_object * new_task = alloc_task(c, prio);
        g_task_manager->enqueue(new_task);
        return new_task;
    }
}

obj_res task_pure(obj_arg a) {
    if (!g_task_manager) {
        return thunk_pure(a);
    } else {
        return alloc_task(a);
    }
}

static obj_res task_map_fn(obj_arg f, obj_arg t, obj_arg) {
    lean_assert(is_thunk(t) || is_task(t));
    b_obj_res v;
    if (is_thunk(t)) v = thunk_get(t); else v = to_task(t)->m_value;
    lean_assert(v != nullptr);
    inc(v);
    dec_ref(t);
    return apply_1(f, v);
}

obj_res task_map(obj_arg f, obj_arg t, unsigned prio) {
    if (!g_task_manager) {
        lean_assert(is_thunk(t));
        return thunk_map(f, t);
    } else {
        task_object * new_task = alloc_task(mk_closure_3_2(task_map_fn, f, t), prio);
        if (is_thunk(t))
            g_task_manager->enqueue(new_task);
        else
            g_task_manager->add_dep(to_task(t), new_task);
        return new_task;
    }
}

b_obj_res task_get(b_obj_arg t) {
    if (is_thunk(t)) {
        return thunk_get(t);
    } else {
        if (object * v = to_task(t)->m_value)
            return v;
        g_task_manager->wait_for(to_task(t));
        lean_assert(to_task(t)->m_value != nullptr);
        object * r = to_task(t)->m_value;
        return r;
    }
}

static obj_res task_bind_fn2(obj_arg t, obj_arg) {
    lean_assert(to_task(t)->m_value);
    b_obj_res v = to_task(t)->m_value;
    inc(v);
    dec_ref(t);
    return v;
}

static obj_res task_bind_fn1(obj_arg x, obj_arg f, obj_arg) {
    lean_assert(is_thunk(x) || is_task(x));
    b_obj_res v;
    if (is_thunk(x)) v = thunk_get(x); else v = to_task(x)->m_value;
    lean_assert(v != nullptr);
    inc(v);
    dec_ref(x);
    obj_res new_task = apply_1(f, v);
    lean_assert(is_thunk(new_task) || is_task(new_task));
    if (is_thunk(new_task)) {
        b_obj_res r = thunk_get(new_task);
        inc(r);
        dec_ref(new_task);
        return r;
    } else {
        lean_assert(is_task(new_task));
        lean_assert(g_current_task_object->m_imp);
        lean_assert(g_current_task_object->m_imp->m_closure == nullptr);
        g_current_task_object->m_imp->m_closure = mk_closure_2_1(task_bind_fn2, new_task);
        g_task_manager->add_dep(to_task(new_task), g_current_task_object);
        return nullptr; /* notify queue that task did not finish yet. */
    }
}

obj_res task_bind(obj_arg x, obj_arg f, unsigned prio) {
    lean_assert(is_thunk(x) || is_task(x));
    if (!g_task_manager) {
        return thunk_bind(x, f);
    } else {
        task_object * new_task = alloc_task(mk_closure_3_2(task_bind_fn1, x, f), prio);
        if (is_thunk(x))
            g_task_manager->enqueue(new_task);
        else
            g_task_manager->add_dep(to_task(x), new_task);
        return new_task;
    }
}

bool io_check_interrupt_core() {
    if (task_object * t = g_current_task_object) {
        lean_assert(t->m_imp); // task is being executed
        return t->m_imp->m_interrupted;
    }
    return false;
}

void io_request_interrupt_core(b_obj_arg t) {
    lean_assert(is_thunk(t) || is_task(t));
    if (is_thunk(t) || to_task(t)->m_value)
        return;
    g_task_manager->request_interrupt(to_task(t));
}

bool io_has_finished_core(b_obj_arg t) {
    lean_assert(is_thunk(t) || is_task(t));
    return is_thunk(t) || to_task(t)->m_value != nullptr;
}

b_obj_res io_wait_any_core(b_obj_arg task_list) {
    return g_task_manager->wait_any(task_list);
}

void mark_persistent(object * o);
static obj_res mark_persistent_fn(obj_arg o) {
    mark_persistent(o);
    return box(0);
}

void mark_persistent(object * o) {
    if (is_scalar(o) || !is_heap_obj(o)) return;
    o->m_mem_kind = static_cast<unsigned>(object_memory_kind::Persistent);

    switch (get_kind(o)) {
    case object_kind::ScalarArray:
    case object_kind::String:
    case object_kind::MPZ:
        return;
    case object_kind::External: {
        object * fn = alloc_closure(reinterpret_cast<void*>(mark_persistent_fn), 1, 0);
        to_external(o)->m_class->m_foreach(to_external(o)->m_data, fn);
        dec(fn);
        return;
    }
    case object_kind::Task:
        mark_persistent(task_get(o));
        return;
    case object_kind::Constructor: {
        object ** it  = cnstr_obj_cptr(o);
        object ** end = it + cnstr_num_objs(o);
        for (; it != end; ++it) mark_persistent(*it);
        return;
    }
    case object_kind::Closure: {
        object ** it  = closure_arg_cptr(o);
        object ** end = it + closure_num_fixed(o);
        for (; it != end; ++it) mark_persistent(*it);
        return;
    }
    case object_kind::Array: {
        object ** it  = array_cptr(o);
        object ** end = it + array_size(o);
        for (; it != end; ++it) mark_persistent(*it);
        return;
    }
    case object_kind::Thunk:
        if (object * c = to_thunk(o)->m_closure) mark_persistent(c);
        if (object * v = to_thunk(o)->m_value) mark_persistent(v);
        return;
    case object_kind::Ref:
        if (object * v = to_ref(o)->m_value) mark_persistent(v);
        return;
    }
}

// =======================================
// Natural numbers

size_t size_t_of_nat(b_obj_arg n) {
    if (is_scalar(n)) {
        return unbox(n);
    } else if (mpz_value(n).is_unsigned_long_int()) {
        return static_cast<size_t>(mpz_value(n).get_unsigned_long_int());
    } else {
        return std::numeric_limits<size_t>::max();
    }
}

object * nat_big_add(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj_core(unbox(a1) + mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj_core(mpz_value(a1) + unbox(a2));
    else
        return mk_nat_obj_core(mpz_value(a1) + mpz_value(a2));
}

object * nat_big_sub(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2));
        return box(0);
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return mk_nat_obj(mpz_value(a1) - unbox(a2));
    } else {
        if (mpz_value(a1) < mpz_value(a2))
            return box(0);
        else
            return mk_nat_obj(mpz_value(a1) - mpz_value(a2));
    }
}

object * nat_big_mul(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj_core(unbox(a1) * mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj_core(mpz_value(a1) * unbox(a2));
    else
        return mk_nat_obj_core(mpz_value(a1) * mpz_value(a2));
}

object * nat_big_div(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        lean_assert(unbox(a1) / mpz_value(a2) == 0);
        return box(0);
    } else if (is_scalar(a2)) {
        usize n2 = unbox(a2);
        return n2 == 0 ? a2 : mk_nat_obj(mpz_value(a1) / mpz(n2));
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mk_nat_obj(mpz_value(a1) / mpz_value(a2));
    }
}

object * nat_big_mod(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        return a1;
    } else if (is_scalar(a2)) {
        usize n2 = unbox(a2);
        return n2 == 0 ? a2 : box((mpz_value(a1) % mpz(n2)).get_unsigned_int());
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mk_nat_obj(mpz_value(a1) % mpz_value(a2));
    }
}

bool nat_big_eq(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) != mpz_value(a2))
        return false;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) != unbox(a2))
        return false;
    } else {
        return mpz_value(a1) == mpz_value(a2);
    }
}

bool nat_big_le(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2))
        return true;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return false;
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

bool nat_big_lt(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2));
        return true;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return false;
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

object * nat_big_land(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) & mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) & mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) & mpz_value(a2));
}

object * nat_big_lor(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) | mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) | mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) | mpz_value(a2));
}

object * nat_big_lxor(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) ^ mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) ^ mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) ^ mpz_value(a2));
}

// =======================================
// Integers

object * int_big_add(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) + mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) + int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) + mpz_value(a2));
}

object * int_big_sub(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) - mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) - int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) - mpz_value(a2));
}

object * int_big_mul(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) * mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) * int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) * mpz_value(a2));
}

object * int_big_div(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) / mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) / int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) / mpz_value(a2));
}



object * int_big_mod(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(mpz(int2int(a1)) % mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) % mpz(int2int(a2)));
    else
        return mk_int_obj(mpz_value(a1) % mpz_value(a2));
}

bool int_big_eq(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(int2int(a1) != mpz_value(a2))
        return false;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) != int2int(a2))
        return false;
    } else {
        return mpz_value(a1) == mpz_value(a2);
    }
}

bool int_big_le(object * a1, object * a2) {
    if (is_scalar(a1)) {
        return int2int(a1) <= mpz_value(a2);
    } else if (is_scalar(a2)) {
        return mpz_value(a1) <= int2int(a2);
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

bool int_big_lt(object * a1, object * a2) {
    if (is_scalar(a1)) {
        return int2int(a1) < mpz_value(a2);
    } else if (is_scalar(a2)) {
        return mpz_value(a1) < int2int(a2);
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

// =======================================
// UInt

uint8 uint8_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 8);
    return static_cast<uint8>(r.get_unsigned_int());
}
uint16 uint16_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 16);
    return static_cast<uint16>(r.get_unsigned_int());
}
uint32 uint32_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 32);
    return static_cast<uint32>(r.get_unsigned_int());
}
uint64 uint64_of_big_nat(b_obj_arg a) {
    mpz r;
    mod2k(r, mpz_value(a), 64);
    if (sizeof(void*) == 8) {
        // 64 bit
        return static_cast<uint64>(r.get_unsigned_long_int());
    } else {
        // 32 bit
        mpz l;
        mod2k(l, r, 32);
        mpz h;
        div2k(h, r, 32);
        return (static_cast<uint64>(h.get_unsigned_int()) << 32) + static_cast<uint64>(l.get_unsigned_int());
    }
}

usize usize_of_big_nat(b_obj_arg a) {
    if (sizeof(void*) == 8)
        return uint64_of_big_nat(a);
    else
        return uint32_of_big_nat(a);
}

usize usize_mix_hash(usize a1, usize a2) {
    if (sizeof(void*) == 8)
        return hash(static_cast<uint64>(a1), static_cast<uint64>(a2));
    else
        return hash(static_cast<uint32>(a1), static_cast<uint32>(a2));
}

// =======================================
// Strings

static inline char * w_string_cstr(object * o) { lean_assert(is_string(o)); return reinterpret_cast<char *>(o) + sizeof(string_object); }

static object * string_ensure_capacity(object * o, size_t extra) {
    lean_assert(is_exclusive(o));
    size_t sz  = string_size(o);
    size_t cap = string_capacity(o);
    if (sz + extra > cap) {
        object * new_o = alloc_string(sz, cap + sz + extra, string_len(o));
        lean_assert(string_capacity(new_o) >= sz + extra);
        memcpy(w_string_cstr(new_o), string_cstr(o), sz);
        free_string_obj(o);
        return new_o;
    } else {
        return o;
    }
}

object * mk_string(char const * s) {
    size_t sz  = strlen(s);
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = alloc_string(rsz, rsz, len);
    memcpy(w_string_cstr(r), s, sz+1);
    return r;
}

object * mk_string(std::string const & s) {
    size_t sz  = s.size();
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = alloc_string(rsz, rsz, len);
    memcpy(w_string_cstr(r), s.data(), sz);
    w_string_cstr(r)[sz] = 0;
    return r;
}

std::string string_to_std(b_obj_arg o) {
    lean_assert(string_size(o) > 0);
    return std::string(w_string_cstr(o), string_size(o) - 1);
}

static size_t mk_capacity(size_t sz) {
    return sz*2;
}

object * string_push(object * s, unsigned c) {
    size_t sz  = string_size(s);
    size_t len = string_len(s);
    object * r;
    if (!is_exclusive(s)) {
        r = alloc_string(sz, mk_capacity(sz+5), len);
        memcpy(w_string_cstr(r), string_cstr(s), sz - 1);
        dec_ref(s);
    } else {
        r = string_ensure_capacity(s, 5);
    }
    unsigned consumed = push_unicode_scalar(w_string_cstr(r) + sz - 1, c);
    to_string(r)->m_size   = sz + consumed;
    to_string(r)->m_length++;
    w_string_cstr(r)[sz + consumed - 1] = 0;
    return r;
}

object * string_append(object * s1, object * s2) {
    size_t sz1      = string_size(s1);
    size_t sz2      = string_size(s2);
    size_t len1     = string_len(s1);
    size_t len2     = string_len(s2);
    size_t new_len  = len1 + len2;
    unsigned new_sz = sz1 + sz2 - 1;
    object * r;
    if (!is_exclusive(s1)) {
        r = alloc_string(new_sz, mk_capacity(new_sz), new_len);
        memcpy(w_string_cstr(r), string_cstr(s1), sz1 - 1);
        dec_ref(s1);
    } else {
        lean_assert(s1 != s2);
        r = string_ensure_capacity(s1, sz2-1);
    }
    memcpy(w_string_cstr(r) + sz1 - 1, string_cstr(s2), sz2 - 1);
    to_string(r)->m_size   = new_sz;
    to_string(r)->m_length = new_len;
    w_string_cstr(r)[new_sz - 1] = 0;
    return r;
}

bool string_eq(object * s1, char const * s2) {
    if (string_size(s1) != strlen(s2) + 1)
        return false;
    return std::memcmp(string_cstr(s1), s2, string_size(s1)) == 0;
}

bool string_lt(object * s1, object * s2) {
    size_t sz1 = string_size(s1) - 1; // ignore null char in the end
    size_t sz2 = string_size(s2) - 1; // ignore null char in the end
    int r      = std::memcmp(string_cstr(s1), string_cstr(s2), std::min(sz1, sz2));
    return r < 0 || (r == 0 && sz1 < sz2);
}

static std::string list_as_string(b_obj_arg lst) {
    std::string s;
    b_obj_arg o = lst;
    while (!is_scalar(o)) {
        push_unicode_scalar(s, unbox(cnstr_get(o, 0)));
        o  = cnstr_get(o, 1);
    }
    return s;
}

static obj_res string_to_list_core(std::string const & s, bool reverse = false) {
    buffer<unsigned> tmp;
    utf8_decode(s, tmp);
    if (reverse)
        std::reverse(tmp.begin(), tmp.end());
    obj_res  r = box(0);
    unsigned i = tmp.size();
    while (i > 0) {
        --i;
        obj_res new_r = alloc_cnstr(1, 2, 0);
        cnstr_set(new_r, 0, box(tmp[i]));
        cnstr_set(new_r, 1, r);
        r = new_r;
    }
    return r;
}

obj_res string_mk(obj_arg cs) {
    std::string s = list_as_string(cs);
    dec(cs);
    return mk_string(s);
}

obj_res string_data(obj_arg s) {
    std::string tmp = string_to_std(s);
    dec_ref(s);
    return string_to_list_core(tmp);
}

uint32 string_utf8_get(b_obj_arg s, b_obj_arg i0) {
    if (!is_scalar(i0)) {
        /* If `i0` is not a scalar, then it must be > LEAN_MAX_SMALL_NAT,
           and should not be a valid index.

           Recall that LEAN_MAX_SMALL_NAT is 2^31-1 in 32-bit machines and
           2^63 - 1 in 64-bit ones.

           `i0` would only be a valid index if `s` had more than `LEAN_MAX_SMALL_NAT`
           bytes which is unlikely.

           For example, Linux for 64-bit machines can address at most 256 Tb which
           is less than 2^63 - 1.
        */
        return char_default_value();
    }
    usize i = unbox(i0);
    char const * str = string_cstr(s);
    usize size = string_size(s) - 1;
    if (i >= string_size(s) - 1)
        return char_default_value();
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
    return char_default_value();
}

/* The reference implementation is:
   ```
   def next (s : @& String) (p : @& Pos) : Ppos :=
   let c := get s p in
   p + csize c
   ```
*/
obj_res string_utf8_next(b_obj_arg s, b_obj_arg i0) {
    if (!is_scalar(i0)) {
        /* See comment at string_utf8_get */
        return nat_add(i0, box(1));
    }
    usize i = unbox(i0);
    char const * str = string_cstr(s);
    usize size       = string_size(s) - 1;
    /* `csize c` is 1 when `i` is not a valid position in the reference implementation. */
    if (i >= size) return box(i+1);
    unsigned c = static_cast<unsigned char>(str[i]);
    if ((c & 0x80) == 0)    return box(i+1);
    if ((c & 0xe0) == 0xc0) return box(i+2);
    if ((c & 0xf0) == 0xe0) return box(i+3);
    if ((c & 0xf8) == 0xf0) return box(i+4);
    /* invalid UTF-8 encoded string */
    return box(i+1);
}

static inline bool is_utf8_first_byte(unsigned char c) {
    return (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 || (c & 0xf8) == 0xf0;
}

obj_res string_utf8_extract(b_obj_arg s, b_obj_arg b0, b_obj_arg e0) {
    if (!is_scalar(b0) || !is_scalar(e0)) {
        /* See comment at string_utf8_get */
        return s;
    }
    usize b = unbox(b0);
    usize e = unbox(e0);
    char const * str = string_cstr(s);
    usize sz = string_size(s) - 1;
    if (b >= e || b >= sz) return mk_string("");
    /* In the reference implementation if `b` is not pointing to a valid UTF8
       character start position, the result is the empty string. */
    if (!is_utf8_first_byte(str[b])) return mk_string("");
    if (e > sz) e = sz;
    lean_assert(b < e);
    lean_assert(e > 0);
    /* In the reference implementation if `e` is not pointing to a valid UTF8
       character start position, it is assumed to be at the end. */
    if (e < sz && !is_utf8_first_byte(str[e])) e = sz;
    usize new_sz = e - b;
    lean_assert(new_sz > 0);
    obj_res r = alloc_string(new_sz+1, new_sz+1, 0);
    memcpy(w_string_cstr(r), string_cstr(s) + b, new_sz);
    w_string_cstr(r)[new_sz] = 0;
    to_string(r)->m_length = utf8_strlen(w_string_cstr(r), new_sz);
    return r;
}

obj_res string_utf8_prev(b_obj_arg s, b_obj_arg i0) {
    if (!is_scalar(i0)) {
        /* See comment at string_utf8_get */
        return nat_sub(i0, box(1));
    }
    usize i  = unbox(i0);
    usize sz = string_size(s) - 1;
    if (i == 0 || i > sz) return box(0);
    i--;
    char const * str = string_cstr(s);
    while (!is_utf8_first_byte(str[i])) {
        lean_assert(i > 0);
        i--;
    }
    return box(i);
}

static unsigned get_utf8_char_size_at(std::string const & s, usize i) {
    if (auto sz = get_utf8_first_byte_opt(s[i])) {
        return *sz;
    } else {
        return 1;
    }
}

obj_res string_utf8_set(obj_arg s, b_obj_arg i0, uint32 c) {
    if (!is_scalar(i0)) {
        /* See comment at string_utf8_get */
        return s;
    }
    usize i  = unbox(i0);
    usize sz = string_size(s) - 1;
    if (i >= sz) return s;
    char * str = w_string_cstr(s);
    if (is_exclusive(s)) {
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

usize string_hash(b_obj_arg s) {
    usize sz = string_size(s) - 1;
    char const * str = string_cstr(s);
    return hash_str(sz, str, 11);
}

// =======================================
// ByteArray

obj_res copy_sarray(obj_arg a, bool expand) {
    unsigned esz   = sarray_elem_size(a);
    size_t sz      = sarray_size(a);
    size_t cap     = sarray_capacity(a);
    lean_assert(cap >= sz);
    if (expand) cap = (cap + 1) * 2;
    lean_assert(!expand || cap > sz);
    object * r     = alloc_sarray(esz, sz, cap);
    uint8 * it     = sarray_cptr<uint8>(a);
    uint8 * dest   = sarray_cptr<uint8>(r);
    memcpy(dest, it, esz*sz);
    dec(a);
    return r;
}

obj_res copy_byte_array(obj_arg a) {
    return copy_sarray(a, false);
}

obj_res byte_array_mk(obj_arg a) {
    usize sz      = array_size(a);
    obj_res r     = alloc_sarray(1, sz, sz);
    object ** it  = array_cptr(a);
    object ** end = it + sz;
    uint8 * dest  = sarray_cptr<uint8>(r);
    for (; it != end; ++it, ++dest) {
        *dest = unbox(*it);
    }
    dec(a);
    return r;
}

obj_res byte_array_data(obj_arg a) {
    usize sz       = sarray_size(a);
    obj_res r      = alloc_array(sz, sz);
    uint8 * it     = sarray_cptr<uint8>(a);
    uint8 * end    = it+sz;
    object ** dest = array_cptr(r);
    for (; it != end; ++it, ++dest) {
        *dest = box(*it);
    }
    dec(a);
    return r;
}

obj_res byte_array_push(obj_arg a, uint8 b) {
    object * r;
    if (is_exclusive(a)) {
        if (sarray_capacity(a) > sarray_size(a))
            r = a;
        else
            r = copy_sarray(a, true);
    } else {
        r = copy_sarray(a, sarray_capacity(a) < 2*sarray_size(a) + 1);
    }
    lean_assert(sarray_capacity(r) > sarray_size(r));
    size_t & sz  = to_sarray(r)->m_size;
    uint8 * it   = sarray_cptr<uint8>(r) + sz;
    *it = b;
    sz++;
    return r;
}

// =======================================
// array functions for generated code

object * mk_array(obj_arg n, obj_arg v) {
    size_t sz;
    if (is_scalar(n)) {
        sz = unbox(n);
    } else {
        mpz const & v = mpz_value(n);
        if (!v.is_unsigned_long_int()) throw std::bad_alloc(); // we will run out of memory
        sz = v.get_unsigned_long_int();
        dec(n);
    }
    object * r    = alloc_array(sz, sz);
    object ** it  = array_cptr(r);
    object ** end = it + sz;
    for (; it != end; ++it) {
        *it = v;
    }
    if (sz > 1) inc(v, sz - 1);
    return r;
}

obj_res copy_array(obj_arg a, bool expand) {
    size_t sz      = array_size(a);
    size_t cap     = array_capacity(a);
    lean_assert(cap >= sz);
    if (expand) cap = (cap + 1) * 2;
    lean_assert(!expand || cap > sz);
    object * r     = alloc_array(sz, cap);
    object ** it   = array_cptr(a);
    object ** end  = it + sz;
    object ** dest = array_cptr(r);
    for (; it != end; ++it, ++dest) {
        *dest = *it;
        inc(*it);
    }
    dec(a);
    return r;
}

object * array_push(obj_arg a, obj_arg v) {
    object * r;
    if (is_exclusive(a)) {
        if (array_capacity(a) > array_size(a))
            r = a;
        else
            r = copy_array(a, true);
    } else {
        r = copy_array(a, array_capacity(a) < 2*array_size(a) + 1);
    }
    lean_assert(array_capacity(r) > array_size(r));
    size_t & sz  = to_array(r)->m_size;
    object ** it = array_cptr(r) + sz;
    *it = v;
    sz++;
    return r;
}

// =======================================
// fixpoint

static inline object * ptr_to_weak_ptr(object * p) {
    return reinterpret_cast<object*>(reinterpret_cast<uintptr_t>(p) | 1);
}

static inline object * weak_ptr_to_ptr(object * w) {
    return reinterpret_cast<object*>((reinterpret_cast<uintptr_t>(w) >> 1) << 1);
}

obj_res fixpoint_aux(obj_arg rec, obj_arg weak_k, obj_arg a) {
    object * k = weak_ptr_to_ptr(weak_k);
    inc(k);
    return apply_2(rec, k, a);
}

obj_res fixpoint(obj_arg rec, obj_arg a) {
    object * k = alloc_closure(fixpoint_aux, 2);
    inc(rec);
    closure_set(k, 0, rec);
    closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = apply_2(rec, k, a);
    return r;
}

obj_res fixpoint_aux2(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2) {
    object * k = weak_ptr_to_ptr(weak_k);
    inc(k);
    return apply_3(rec, k, a1, a2);
}

obj_res fixpoint2(obj_arg rec, obj_arg a1, obj_arg a2) {
    object * k = alloc_closure(fixpoint_aux2, 2);
    inc(rec);
    closure_set(k, 0, rec);
    closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = apply_3(rec, k, a1, a2);
    return r;
}

obj_res fixpoint_aux3(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2, obj_arg a3) {
    object * k = weak_ptr_to_ptr(weak_k);
    inc(k);
    return apply_4(rec, k, a1, a2, a3);
}

obj_res fixpoint3(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3) {
    object * k = alloc_closure(fixpoint_aux3, 2);
    inc(rec);
    closure_set(k, 0, rec);
    closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = apply_4(rec, k, a1, a2, a3);
    return r;
}

obj_res fixpoint_aux4(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4) {
    object * k = weak_ptr_to_ptr(weak_k);
    inc(k);
    return apply_5(rec, k, a1, a2, a3, a4);
}

obj_res fixpoint4(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4) {
    object * k = alloc_closure(fixpoint_aux4, 2);
    inc(rec);
    closure_set(k, 0, rec);
    closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = apply_5(rec, k, a1, a2, a3, a4);
    return r;
}

obj_res fixpoint_aux5(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5) {
    object * k = weak_ptr_to_ptr(weak_k);
    inc(k);
    return apply_6(rec, k, a1, a2, a3, a4, a5);
}

obj_res fixpoint5(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5) {
    object * k = alloc_closure(fixpoint_aux5, 2);
    inc(rec);
    closure_set(k, 0, rec);
    closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = apply_6(rec, k, a1, a2, a3, a4, a5);
    return r;
}

obj_res fixpoint_aux6(obj_arg rec, obj_arg weak_k, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5, obj_arg a6) {
    object * k = weak_ptr_to_ptr(weak_k);
    inc(k);
    return apply_7(rec, k, a1, a2, a3, a4, a5, a6);
}

obj_res fixpoint6(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5, obj_arg a6) {
    object * k = alloc_closure(fixpoint_aux6, 2);
    inc(rec);
    closure_set(k, 0, rec);
    closure_set(k, 1, ptr_to_weak_ptr(k));
    object * r = apply_7(rec, k, a1, a2, a3, a4, a5, a6);
    return r;
}

// =======================================
// Runtime info

extern "C" object * lean_closure_max_args(object *) {
    return mk_nat_obj(static_cast<unsigned>(LEAN_CLOSURE_MAX_ARGS));
}

extern "C" object * lean_max_small_nat(object *) {
    return mk_nat_obj(LEAN_MAX_SMALL_NAT);
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

object * dbg_trace(obj_arg s, obj_arg fn) {
    {
        unique_lock<mutex> lock(g_dbg_mutex);
        std::cout << string_cstr(s) << std::endl;
    }
    dec(s);
    return apply_1(fn, box(0));
}

object * dbg_sleep(uint32 ms, obj_arg fn) {
    chrono::milliseconds c(ms);
    this_thread::sleep_for(c);
    return apply_1(fn, box(0));
}

object * dbg_trace_if_shared(obj_arg s, obj_arg a) {
    if (is_heap_obj(a) && is_shared(a)) {
        unique_lock<mutex> lock(g_dbg_mutex);
        std::cout << "shared RC: " << get_rc(a) << ", " << string_cstr(s) << std::endl;
    }
    dec(s);
    return a;
}

// =======================================
// Statistics
#ifdef LEAN_RUNTIME_STATS
atomic<uint64> g_num_ctor(0);
atomic<uint64> g_num_closure(0);
atomic<uint64> g_num_string(0);
atomic<uint64> g_num_array(0);
atomic<uint64> g_num_thunk(0);
atomic<uint64> g_num_task(0);
atomic<uint64> g_num_ext(0);
atomic<uint64> g_num_st_inc(0);
atomic<uint64> g_num_mt_inc(0);
atomic<uint64> g_num_st_dec(0);
atomic<uint64> g_num_mt_dec(0);
atomic<uint64> g_num_del(0);
struct runtime_stats {
    ~runtime_stats() {
        std::cerr << "num. constructors:   " << g_num_ctor << "\n";
        std::cerr << "num. closures:       " << g_num_closure << "\n";
        std::cerr << "num. strings:        " << g_num_string << "\n";
        std::cerr << "num. array:          " << g_num_array << "\n";
        std::cerr << "num. thunk:          " << g_num_thunk << "\n";
        std::cerr << "num. task:           " << g_num_task << "\n";
        std::cerr << "num. external:       " << g_num_ext << "\n";
        std::cerr << "num. ST inc:         " << g_num_st_inc << "\n";
        std::cerr << "num. MT inc:         " << g_num_mt_inc << "\n";
        std::cerr << "num. ST dec:         " << g_num_st_dec << "\n";
        std::cerr << "num. MT dec:         " << g_num_mt_dec << "\n";
        std::cerr << "num. del:            " << g_num_del << "\n";
    }
};
runtime_stats g_runtime_stats;
#endif

// =======================================
// Global constant table

static object * g_decls = nullptr;

/* Remark: this is ugly, it forces the Lean runtime to depend on the implementation of `Lean.Name`.
   This may be an issue for standalone applications. */
extern "C" object* lean_name_mk_string(obj_arg p, obj_arg s);

obj_res mk_const_name(obj_arg p, char const * s) {
    return lean_name_mk_string(p, mk_string(s));
}

/* Remark: we should improve this too. A standalone application implemented in Lean will seldom
   need a table with all constants. This table is only used to implement `Lean.evalConst`
   unsafe primitive. */
void register_constant(obj_arg fn, obj_arg obj) {
    object * p = alloc_cnstr(0, 2, 0);
    cnstr_set(p, 0, fn);
    cnstr_set(p, 1, obj);
    g_decls = array_push(g_decls, p);
}

obj_res set_io_result(obj_arg r, obj_arg a);

extern "C" obj_res lean_modify_constant_table(obj_arg f, obj_arg w) {
    g_decls = apply_1(f, g_decls);
    return w;
}

extern "C" obj_res lean_get_constant_table(obj_arg w) {
    inc(g_decls);
    return set_io_result(w, g_decls);
}

// =======================================
// Module initialization

void initialize_object() {
    g_ext_classes       = new std::vector<external_object_class*>();
    g_ext_classes_mutex = new mutex();
    g_array_empty       = alloc_array(0, 0);
    mark_persistent(g_array_empty);
    g_decls             = alloc_array(0, 8192);
}

void finalize_object() {
    for (external_object_class * cls : *g_ext_classes) delete cls;
    delete g_ext_classes;
    delete g_ext_classes_mutex;
}
}

extern "C" void lean_dbg_print_str(lean::object* o) { lean::dbg_print_str(o); }
extern "C" void lean_dbg_print_num(lean::object* o) { lean::dbg_print_num(o); }
