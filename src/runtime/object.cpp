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

namespace lean {
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
    case object_kind::PArrayRoot:      return sizeof(parray_object);
    case object_kind::PArraySet:       return sizeof(parray_object);
    case object_kind::PArrayPush:      return sizeof(parray_object);
    case object_kind::PArrayPop:       return sizeof(parray_object);
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
    case object_kind::PArrayRoot:      return sizeof(parray_object);
    case object_kind::PArraySet:       return sizeof(parray_object);
    case object_kind::PArrayPush:      return sizeof(parray_object);
    case object_kind::PArrayPop:       return sizeof(parray_object);
    case object_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

/* We use the RC memory to implement a linked list of lean objects to be deleted.
   This hack is safe because rc_type is uintptr_t. */

static_assert(sizeof(atomic<rc_type>) == sizeof(object*),  "unexpected atomic<rc_type> size, the object GC assumes these two types have the same size"); // NOLINT

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

static size_t parray_data_capacity(object ** data) {
    return reinterpret_cast<size_t*>(data)[-1];
}

static object ** alloc_parray_data(size_t c) {
    size_t * mem = static_cast<size_t*>(malloc(sizeof(object*)*c + sizeof(size_t)));
    *mem = c;
    mem++;
    return reinterpret_cast<object**>(mem);
}

static void dealloc_parray_data(object ** data) {
    size_t * mem = reinterpret_cast<size_t*>(data);
    mem--;
    free(mem);
}

void del(object * o) {
    object * todo = nullptr;
    while (true) {
        lean_assert(is_heap_obj(o));
        switch (get_kind(o)) {
        case object_kind::Constructor: {
            object ** it  = cnstr_obj_cptr(o);
            object ** end = it + cnstr_num_objs(o);
            for (; it != end; ++it) dec(*it, todo);
            free_heap_obj(o);
            break;
        }
        case object_kind::Closure: {
            object ** it  = closure_arg_cptr(o);
            object ** end = it + closure_num_fixed(o);
            for (; it != end; ++it) dec(*it, todo);
            free_heap_obj(o);
            break;
        }
        case object_kind::Array: {
            object ** it  = array_cptr(o);
            object ** end = it + array_size(o);
            for (; it != end; ++it) dec(*it, todo);
            free_heap_obj(o);
            break;
        }
        case object_kind::ScalarArray:
            free_heap_obj(o); break;
        case object_kind::String:
            free_heap_obj(o); break;
        case object_kind::MPZ:
            dealloc_mpz(o); break;
        case object_kind::Thunk:
            if (object * c = to_thunk(o)->m_closure) dec(c, todo);
            if (object * v = to_thunk(o)->m_value) dec(v, todo);
            free_heap_obj(o);
            break;
        case object_kind::Task:
            deactivate_task(to_task(o));
            break;
        case object_kind::PArrayPop:
            dec_ref(to_parray(o)->m_next, todo);
            free_heap_obj(o);
            break;
        case object_kind::PArrayPush:
        case object_kind::PArraySet:
            dec(to_parray(o)->m_elem, todo);
            dec_ref(to_parray(o)->m_next, todo);
            free_heap_obj(o);
            break;
        case object_kind::PArrayRoot: {
            object ** it  = to_parray(o)->m_data;
            object ** end = it + to_parray(o)->m_size;
            for (; it != end; ++it) dec(*it, todo);
            dealloc_parray_data(to_parray(o)->m_data);
            free_heap_obj(o);
            break;
        }
        case object_kind::External:
            dealloc_external(o); break;
        }
        /* We can use a counter to avoid pauses at `del` when many objects
           are reachable from `o` need to be deleted.
           The idea is to have a threshold on the maximum number of elements
           that can be deleted in a single round. */
        if (todo == nullptr)
            return;
        o = pop_back(todo);
    }
}

// =======================================
// Scalar arrays

#if 0
static object * sarray_ensure_capacity(object * o, size_t extra) {
    lean_assert(!is_exclusive(o));
    size_t sz  = sarray_size(o);
    size_t cap = sarray_capacity(o);
    if (sz + extra > cap) {
        unsigned esize = sarray_elem_size(o);
        object * new_o = alloc_sarray(esize, sz, cap + sz + extra);
        lean_assert(sarray_capacity(new_o) >= sz + extra);
        memcpy(sarray_cptr<char>(new_o), sarray_cptr<char>(o), esize * sz);
        free_heap_obj(o);
        return new_o;
    } else {
        return o;
    }
}
#endif

// =======================================
// Persistent arrays

static object ** parray_data_expand(object ** data, size_t sz) {
    size_t curr_capacity = parray_data_capacity(data);
    size_t new_capacity  = curr_capacity == 0 ? 2 : (3 * curr_capacity + 1) >> 1;
    object ** new_data   = alloc_parray_data(new_capacity);
    memcpy(new_data, data, sizeof(object*)*sz);
    dealloc_parray_data(data);
    return new_data;
}

/* Given `c -> ... -> root`,
   revert links and make `c` to be the new root:
   `c <- ... <- root` */
static void parray_reroot(object * c) {
    lean_assert(get_kind(c) != object_kind::PArrayRoot);
    parray_object * it   = to_parray(c);
    parray_object * prev = nullptr;
    /* invert links */
    while (get_kind(it) != object_kind::PArrayRoot) {
        /* c <- ... <- prev, it -> it_next -> ... -> root
           c <- ... <- prev <- it, it_next -> ... -> root */
        parray_object * it_next = it->m_next;
        it->m_next = prev;
        prev = it;
        it   = it_next;
    }
    lean_assert(prev != nullptr);
    lean_assert(get_kind(it) == object_kind::PArrayRoot);
    lean_assert(it != c);
    object * old_root = it;
    it->m_next = prev;
    object ** data = it->m_data;
    size_t sz = it->m_size;
    prev = it;
    it   = it->m_next;
    /* move array to `c` */
    while (true) {
        lean_assert(prev != nullptr && it != prev);
        switch (get_kind(it)) {
        case object_kind::PArraySet:
            prev->m_kind = static_cast<unsigned>(object_kind::PArraySet);
            prev->m_idx  = it->m_idx;
            prev->m_elem = data[it->m_idx];
            data[it->m_idx] = it->m_elem;
            break;
        case object_kind::PArrayPush:
            if (sz == parray_data_capacity(data))
                data = parray_data_expand(data, sz);
            prev->m_kind = static_cast<unsigned>(object_kind::PArrayPop);
            data[sz]   = it->m_elem;
            sz++;
            break;
        case object_kind::PArrayPop:
            --sz;
            prev->m_kind = static_cast<unsigned>(object_kind::PArrayPush);
            prev->m_elem = data[sz];
            break;
        default:
            lean_unreachable();
        }
        if (it == c)
            break;
        prev = it;
        it   = it->m_next;
    }
    lean_assert(it == c);
    it->m_kind = static_cast<unsigned>(object_kind::PArrayRoot);
    it->m_data = data;
    it->m_size = sz;
    dec_ref(old_root);
    inc_ref(c);
}

static parray_object * move_parray_root(parray_object * src) {
    lean_assert(src->m_kind == static_cast<unsigned>(object_kind::PArrayRoot));
    lean_assert(get_rc(src) > 1);
    dec_ref(src);
    parray_object * r = new (alloc_heap_object(sizeof(parray_object))) parray_object();
    r->m_data = src->m_data;
    r->m_size = src->m_size;
    return r;
}

obj_res alloc_parray(size_t capacity) {
    parray_object * r = new (alloc_heap_object(sizeof(parray_object))) parray_object();
    r->m_data = alloc_parray_data(capacity);
    r->m_size = 0;
    return r;
}

size_t parray_size(b_obj_arg o) {
    if (get_kind(o) != object_kind::PArrayRoot)
        parray_reroot(o);
    return to_parray(o)->m_size;
}

b_obj_res parray_get(b_obj_arg o, size_t i) {
    if (get_kind(o) != object_kind::PArrayRoot)
        parray_reroot(o);
    return to_parray(o)->m_data[i];
}

obj_res parray_set(obj_arg o, size_t i, obj_arg v) {
    if (get_kind(o) != object_kind::PArrayRoot)
        parray_reroot(o);
    parray_object * p = to_parray(o);
    if (get_rc(p) == 1) {
        dec(p->m_data[i]);
        p->m_data[i] = v;
        return p;
    } else {
        parray_object * r = move_parray_root(p);
        p->m_kind    = static_cast<unsigned>(object_kind::PArraySet);
        p->m_idx     = i;
        p->m_elem    = r->m_data[i];
        p->m_next    = r;
        inc_ref(r);
        r->m_data[i] = v;
        return r;
    }
}

obj_res parray_push(obj_arg o, obj_arg v) {
    if (get_kind(o) != object_kind::PArrayRoot)
        parray_reroot(o);
    parray_object * p = to_parray(o);
    if (p->m_size == parray_data_capacity(p->m_data))
        p->m_data = parray_data_expand(p->m_data, p->m_size);
    if (get_rc(p) == 1) {
        p->m_data[p->m_size] = v;
        p->m_size++;
        return p;
    } else {
        parray_object * r = move_parray_root(p);
        p->m_kind = static_cast<unsigned>(object_kind::PArrayPop);
        p->m_next = r;
        inc_ref(r);
        r->m_data[r->m_size] = v;
        r->m_size++;
        return r;
    }
}

obj_res parray_pop(obj_arg o) {
    if (get_kind(o) != object_kind::PArrayRoot)
        parray_reroot(o);
    parray_object * p = to_parray(o);
    if (get_rc(p) == 1) {
        p->m_size--;
        dec(p->m_data[p->m_size]);
        return p;
    } else {
        parray_object * r = move_parray_root(p);
        r->m_size--;
        p->m_kind = static_cast<unsigned>(object_kind::PArrayPush);
        p->m_elem = r->m_data[r->m_size];
        p->m_next = r;
        inc_ref(r);
        return r;
    }
}

obj_res parray_copy(b_obj_arg o) {
    if (get_kind(o) != object_kind::PArrayRoot)
        parray_reroot(o);
    size_t sz      = to_parray(o)->m_size;
    object ** data = to_parray(o)->m_data;
    parray_object * r = new (alloc_heap_object(sizeof(parray_object))) parray_object();
    r->m_size = sz;
    r->m_data = alloc_parray_data(parray_data_capacity(data));
    memcpy(r->m_data, data, sz);
    for (size_t i = 0; i < sz; i++)
        inc(data[i]);
    return r;
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
    free_heap_obj(t);
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
    std::map<unsigned, std::deque<task_object *>> m_queue;
    condition_variable                            m_queue_cv;
    condition_variable                            m_task_finished_cv;
    bool                                          m_shutting_down{false};

    task_object * dequeue() {
        lean_assert(!m_queue.empty());
        auto it                   = m_queue.begin();
        auto & highest_prio_deque = it->second;
        task_object * result      = highest_prio_deque.front();
        highest_prio_deque.pop_front();
        if (highest_prio_deque.empty())
            m_queue.erase(it);
        return result;
    }

    void enqueue_core(task_object * t) {
        lean_assert(t->m_imp);
        m_queue[t->m_imp->m_prio].push_back(t);
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

                        if (m_queue.empty()) {
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
        for (std::pair<const unsigned, std::deque<task_object *>> & entry : m_queue) {
            for (task_object * o : entry.second) {
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
            free_heap_obj(t);
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

task_object::task_object(obj_arg c, unsigned prio):
    object(object_kind::Task, object_memory_kind::STHeap), m_value(nullptr), m_imp(new imp(c, prio)) {
    lean_assert(is_closure(c));
}

task_object::task_object(obj_arg v):
    object(object_kind::Task, object_memory_kind::STHeap), m_value(v), m_imp(nullptr) {
}

static task_object * alloc_task(obj_arg c, unsigned prio) {
    return new (alloc_heap_object(sizeof(task_object))) task_object(c, prio); // NOLINT
}

static task_object * alloc_task(obj_arg v) {
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
        unsigned n2 = unbox(a2);
        return n2 == 0 ? a2 : mk_nat_obj(mpz_value(a1) / n2);
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
        unsigned n2 = unbox(a2);
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

object * int_big_rem(object * a1, object * a2) {
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
        free_heap_obj(o);
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
    lean_assert(s1 != s2);
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
        r = string_ensure_capacity(s1, sz2-1);
    }
    memcpy(w_string_cstr(r) + sz1 - 1, string_cstr(s2), sz2 - 1);
    to_string(r)->m_size   = new_sz;
    to_string(r)->m_length = new_len;
    w_string_cstr(r)[new_sz - 1] = 0;
    return r;
}

bool string_eq(object * s1, object * s2) {
    if (string_size(s1) != string_size(s2))
        return false;
    return std::memcmp(string_cstr(s1), string_cstr(s2), string_size(s1)) == 0;
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

static std::string rev_list_as_string(b_obj_arg lst) {
    buffer<unsigned> codes;
    b_obj_arg o = lst;
    while (!is_scalar(o)) {
        codes.push_back(unbox(cnstr_get(o, 0)));
        o  = cnstr_get(o, 1);
    }
    std::reverse(codes.begin(), codes.end());
    std::string s;
    for (unsigned c : codes) {
        push_unicode_scalar(s, c);
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
    std::string tmp(string_cstr(s), string_size(s));
    dec_ref(s);
    return string_to_list_core(tmp);
}

/* `pos` is in bytes, and `remaining` is in characters */
static obj_res mk_iterator(obj_arg s, size_t pos, size_t remaining) {
    obj_res r = alloc_cnstr(0, 1, sizeof(size_t)*2);
    cnstr_set(r, 0, s);
    cnstr_set_scalar<size_t>(r, sizeof(object*), pos);
    cnstr_set_scalar<size_t>(r, sizeof(object*)+sizeof(size_t), remaining);
    return r;
}

static b_obj_res it_string(b_obj_arg it) { return cnstr_get(it, 0); }
static size_t it_pos(b_obj_arg it) { return cnstr_get_scalar<size_t>(it, sizeof(object*)); }
static size_t it_remaining(b_obj_arg it) { return cnstr_get_scalar<size_t>(it, sizeof(object*)+sizeof(size_t)); }
static void it_set_string(u_obj_arg it, obj_arg s) { cnstr_set(it, 0, s); }
static void it_set_pos(u_obj_arg it, size_t pos) { cnstr_set_scalar<size_t>(it, sizeof(object*), pos); }
static void it_set_remaining(u_obj_arg it, size_t r) { cnstr_set_scalar<size_t>(it, sizeof(object*)+sizeof(size_t), r); }
/* instance : inhabited char := ⟨'A'⟩ */
static uint32 mk_default_char() { return 65; }
static bool is_unshared_it_string(b_obj_arg it) { return is_exclusive(it) && !is_shared(cnstr_get(it, 0)); }

static unsigned get_utf8_char_size_at(std::string const & s, unsigned i) {
    if (auto sz = is_utf8_first_byte(s[i])) {
        return *sz;
    } else {
        return 1;
    }
}

obj_res string_mk_iterator(obj_arg s) {
    return mk_iterator(s, 0, string_len(s));
}

uint32 string_iterator_curr(b_obj_arg it) {
    object * s = it_string(it);
    size_t i   = it_pos(it);
    if (i < string_size(s)) {
        return next_utf8(string_cstr(s), i);
    } else {
        return mk_default_char();
    }
}

/* def set_curr : iterator → char → iterator */
obj_res string_iterator_set_curr(obj_arg it, uint32 c) {
    object * s = it_string(it);
    size_t i   = it_pos(it);
    if (i >= string_size(s)) {
        /* at end */
        return it;
    }
    if (is_unshared_it_string(it)) {
        if (static_cast<unsigned char>(string_cstr(s)[i]) < 128 && c < 128) {
            /* easy case, old and new characters are encoded using 1 byte */
            w_string_cstr(s)[i] = c;
            return it;
        }
    }
    /* TODO(Leo): improve performance of the special cases.
       Example: `it` is not shared, but string is; new and old characters have the same size; etc. */
    std::string tmp;
    push_unicode_scalar(tmp, c);
    std::string new_s(string_cstr(s), string_size(s));
    new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
    size_t rem = it_remaining(it);
    dec_ref(it);
    return mk_iterator(mk_string(new_s), i, rem);
}

/* def next : iterator → iterator */
obj_res string_iterator_next(obj_arg it) {
    object * s = it_string(it);
    size_t i   = it_pos(it);
    size_t r   = it_remaining(it);
    if (i < string_size(s)) {
        next_utf8(string_cstr(s), i);
        if (is_exclusive(it)) {
            it_set_pos(it, i);
            it_set_remaining(it, r-1);
            return it;
        } else {
            inc_ref(s);
            obj_res new_it = mk_iterator(s, i, r-1);
            dec_ref(it);
            return new_it;
        }
    } else {
        return it;
    }
}

/* def prev : iterator → iterator */
obj_res string_iterator_prev(obj_arg it) {
    object * s = it_string(it);
    size_t i   = it_pos(it);
    size_t r   = it_remaining(it);
    if (i > 0) {
        size_t new_i = i;
        /* we have to walk at most 4 steps backwards */
        for (unsigned j = 0; j < 4; j++) {
            --new_i;
            if (is_utf8_first_byte(string_cstr(s)[new_i])) {
                if (is_exclusive(it)) {
                    it_set_pos(it, new_i);
                    it_set_remaining(it, r+1);
                    return it;
                } else {
                    inc_ref(s);
                    obj_res new_it = mk_iterator(s, new_i, r+1);
                    dec_ref(it);
                    return new_it;
                }
            }
        }
        /* incorrectly encoded utf-8 string */
        return it;
    } else {
        return it;
    }
}

/* def has_next : iterator → bool */
uint8 string_iterator_has_next(b_obj_arg it) {
    return it_pos(it) < string_size(it_string(it));
}

/* def has_prev : iterator → bool */
uint8 string_iterator_has_prev(b_obj_arg it) {
    return it_pos(it) > 0;
}

obj_res string_iterator_remaining(b_obj_arg it) {
    return nat_of_size_t(it_remaining(it));
}

obj_res string_iterator_offset(b_obj_arg it) {
    size_t len = string_len(it_string(it));
    size_t rem = it_remaining(it);
    return nat_of_size_t(len - rem);
}

/* def to_string : iterator → string */
obj_res string_iterator_to_string(b_obj_arg it) {
    object * s = it_string(it);
    inc_ref(s);
    return s;
}

/* def to_end : iterator → iterator */
obj_res string_iterator_to_end(obj_arg it) {
    object * s = it_string(it);
    if (is_exclusive(it)) {
        it_set_pos(it, string_size(s));
        it_set_remaining(it, 0);
        return it;
    } else {
        inc_ref(s);
        obj_res new_it = mk_iterator(s, string_size(s), 0);
        dec_ref(it);
        return new_it;
    }
}

/* def remaining_to_string : iterator → string */
obj_res string_iterator_remaining_to_string(b_obj_arg it) {
    object * s = it_string(it);
    size_t i   = it_pos(it);
    std::string r;
    for (; i < string_size(s); i++) {
        r += string_cstr(s)[i];
    }
    return mk_string(r);
}

/* def prev_to_string : iterator → string */
obj_res string_iterator_prev_to_string(b_obj_arg it) {
    object * s = it_string(it);
    size_t pos = it_pos(it);
    std::string r;
    for (size_t i = 0; i < pos; i++) {
        r += string_cstr(s)[i];
    }
    return mk_string(r);
}

/* def insert : iterator → string → iterator */
obj_res string_iterator_insert(obj_arg it, b_obj_arg s) {
    object * s_0 = it_string(it);
    object * s_1 = s;
    size_t i     = it_pos(it);
    size_t r     = it_remaining(it);
    if (i >= string_size(s_0)) {
        /* insert s in the end */
        if (is_unshared_it_string(it)) {
            object * new_s = string_append(s_0, s_1);
            it_set_string(it, new_s);
            it_set_remaining(it, r + string_len(s_1));
            return it;
        } else {
            inc_ref(s_0);
            object * new_s = string_append(s_0, s_1);
            dec_ref(it);
            return mk_iterator(new_s, i, r + string_len(s_1));
        }
    } else {
        /* insert in the middle */
        /* TODO(Leo): optimize is_unshared_it_string(it) case */
        std::string new_s(string_cstr(s_0), string_size(s_0));
        new_s.insert(i, std::string(string_cstr(s_1), string_size(s_1)));
        dec_ref(it);
        return mk_iterator(mk_string(new_s), i, r + string_len(s_1));
    }
}

/* def remove : iterator → nat → iterator */
obj_res string_iterator_remove(obj_arg it, b_obj_arg n0) {
    object * s     = it_string(it);
    size_t sz      = string_size(s);
    size_t i       = it_pos(it);
    size_t j       = i;
    size_t n       = size_t_of_nat(n0);
    size_t new_len = string_len(s);
    size_t r       = it_remaining(it);
    for (size_t k  = 0; k < n && j < sz; k++) {
        next_utf8(string_cstr(s), j);
        new_len--;
        r--;
    }
    size_t count   = j - i;
    /* TODO(Leo): optimize case wher is_unshared_it_string(it) */
    std::string new_s(string_cstr(s), sz);
    new_s.erase(i, count);
    dec_ref(it);
    return mk_iterator(mk_string(new_s), i, r);
}

/* def extract : iterator → iterator → option string */
obj_res string_iterator_extract(b_obj_arg it1, b_obj_arg it2) {
    object * s1 = it_string(it1);
    object * s2 = it_string(it2);
    if (&s1 != &s2 && string_ne(s1, s2))
        return mk_option_none();
    size_t pos1 = it_pos(it1);
    size_t pos2 = it_pos(it2);
    if (pos2 < pos1)
        return mk_option_none();
    size_t new_sz = pos2 - pos1;
    object * r = alloc_cnstr(new_sz, new_sz, it_remaining(it1) - it_remaining(it2));
    memcpy(w_string_cstr(r), string_cstr(s1) + pos1, new_sz);
    return mk_option_some(r);
}

obj_res string_iterator_mk(b_obj_arg l1, b_obj_arg l2) {
    std::string s1 = rev_list_as_string(l1);
    std::string s2 = list_as_string(l2);
    size_t i       = s1.size();
    std::reverse(s1.begin(), s1.end());
    s1 += s2;
    return mk_iterator(mk_string(s1), i, utf8_strlen(s2));
}

obj_res string_iterator_fst(b_obj_arg it) {
    object * s = string_iterator_prev_to_string(it);
    object * r = string_to_list_core(std::string(string_cstr(s), string_size(s)), true /* reverse */);
    dec_ref(s);
    return r;
}

obj_res string_iterator_snd(b_obj_arg it) {
    object * s = string_iterator_remaining_to_string(it);
    object * r = string_to_list_core(std::string(string_cstr(s), string_size(s)));
    dec_ref(s);
    return r;
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
}

extern "C" void lean_dbg_print_str(lean::object* o) { lean::dbg_print_str(o); }
extern "C" void lean_dbg_print_num(lean::object* o) { lean::dbg_print_num(o); }
