/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include <vector>
#include "runtime/compact.h"

#define LEAN_COMPACTOR_INIT_SZ 1024*1024

namespace lean {
#define TERMINATOR_ID (static_cast<unsigned>(object_kind::External) + 1)

// special object that terminates the data block constructing the object graph rooted in `m_value`
struct terminator_object : public object {
    object * m_value;

    explicit terminator_object(object * value) : object(object_kind::External, object_memory_kind::Region), m_value(value) {
        // not an actual `object_kind`, so write to the field directly
        m_kind = TERMINATOR_ID;
    }
};

object_compactor::object_compactor():
    m_begin(malloc(LEAN_COMPACTOR_INIT_SZ)),
    m_end(m_begin),
    m_capacity(static_cast<char*>(m_begin) + LEAN_COMPACTOR_INIT_SZ) {
}

object_compactor::~object_compactor() {
    free(m_begin);
}

object_offset g_null_offset = reinterpret_cast<object_offset>(static_cast<size_t>(-1));

void * object_compactor::alloc(size_t sz) {
    size_t rem = sz % sizeof(void*);
    if (rem != 0)
        sz = sz + sizeof(void*) - rem;
    while (static_cast<char*>(m_end) + sz > m_capacity) {
        size_t new_capacity = capacity()*2;
        void * new_begin = malloc(new_capacity);
        memcpy(new_begin, m_begin, size());
        m_end      = static_cast<char*>(new_begin) + size();
        m_capacity = static_cast<char*>(new_begin) + new_capacity;
        free(m_begin);
        m_begin    = new_begin;
    }
    void * r = m_end;
    m_end = static_cast<char*>(m_end) + sz;
    lean_assert(m_end <= m_capacity);
    return r;
}

object_offset object_compactor::to_offset(object * o) {
    if (is_scalar(o)) {
        return o;
    } else {
        auto it = m_obj_table.find(o);
        if (it == m_obj_table.end()) {
            m_todo.push_back(o);
            return g_null_offset;
        } else {
            return it->second;
        }
    }
}

void object_compactor::insert_terminator(object * o) {
    void * mem = alloc(sizeof(terminator_object));
    new (mem) terminator_object(to_offset(o));
}

object * object_compactor::copy_object(object * o) {
    size_t sz = obj_byte_size(o);
    void * mem = alloc(sz);
    memcpy(mem, o, sz);
    object * r = static_cast<object*>(mem);
    r->m_mem_kind = static_cast<unsigned>(object_memory_kind::Region);
    save(o, r);
    return r;
}

bool object_compactor::insert_constructor(object * o) {
    std::vector<object_offset> & offsets = m_tmp;
    offsets.clear();
    bool missing_children = false;
    unsigned num_objs     = cnstr_num_objs(o);
    for (unsigned i = 0; i < num_objs; i++) {
        object_offset c = to_offset(cnstr_get(o, i));
        if (c == g_null_offset)
            missing_children = true;
        offsets.push_back(c);
    }
    if (missing_children)
        return false;
    object * new_o = copy_object(o);
    for (unsigned i = 0; i < cnstr_num_objs(o); i++)
        cnstr_set(new_o, i, offsets[i]);
    return true;
}

bool object_compactor::insert_array(object * o) {
    std::vector<object_offset> & offsets = m_tmp;
    offsets.clear();
    bool missing_children = false;
    size_t sz = array_size(o);
    for (size_t i = 0; i < sz; i++) {
        object_offset c = to_offset(array_get(o, i));
        if (c == g_null_offset)
            missing_children = true;
        offsets.push_back(c);
    }
    if (missing_children)
        return false;
    void * mem = alloc(sizeof(array_object) + sz * sizeof(object *));
    object * new_o = new (mem) array_object(sz, sz, object_memory_kind::Region);
    for (size_t i = 0; i < sz; i++) {
        array_set(new_o, i, offsets[i]);
    }
    save(o, new_o);
    return true;
}

bool object_compactor::insert_thunk(object * o) {
    object * v = thunk_get(o);
    object_offset c = to_offset(v);
    if (c == g_null_offset)
        return false;
    object * r = copy_object(o);
    to_thunk(r)->m_value = c;
    return true;
}

bool object_compactor::insert_ref(object * o) {
    object * v = to_ref(o)->m_value;
    object_offset c = to_offset(v);
    if (c == g_null_offset)
        return false;
    object * r = copy_object(o);
    to_ref(r)->m_value = c;
    return true;
}

bool object_compactor::insert_task(object * o) {
    object * v = task_get(o);
    object_offset c = to_offset(v);
    if (c == g_null_offset)
        return false;
    /* We save the task as a thunk.
       Reason: when multi-threading is disabled the task primitives
       create thunk objects instead of task objects. This may create
       problems when there is a mismatch when creating and reading a
       compacted region. For example, multi-threading support was
       enabled when creating the region, and disabled when reading it.
       To cope with this issue, we always save tasks as thunks,
       and rely on the fact that all task API accepts thunks as arguments
       even when multi-threading is enabled. */
    void * mem     = alloc(sizeof(thunk_object));
    object * new_o = new (mem) thunk_object(c, true, object_memory_kind::Region);
    save(o, new_o);
    return true;
}

void object_compactor::insert_mpz(object * o) {
    std::string s       = mpz_value(o).to_string();
    /* Remark: in the compacted_region object, we use the space after the mpz_object
       to store the next mpz_object in the region AFTER we convert the string back
       into an mpz number. So, we use std::max to make sure we have enough space for both. */
    size_t extra_space  = std::max(s.size() + 1, sizeof(mpz_object*));
    void * mem     = alloc(sizeof(mpz_object) + extra_space);
    object * new_o = new (mem) object(object_kind::MPZ, object_memory_kind::Region);
    save(o, new_o);
    void * data    = reinterpret_cast<char*>(new_o) + sizeof(mpz_object);
    memcpy(data, s.c_str(), s.size() + 1);
}

void object_compactor::operator()(object * o) {
    lean_assert(m_todo.empty());
    if (!is_scalar(o)) {
        m_todo.push_back(o);
        while (!m_todo.empty()) {
            object * curr = m_todo.back();
            if (m_obj_table.find(curr) != m_obj_table.end()) {
                m_todo.pop_back();
                continue;
            }
            lean_assert(!is_scalar(curr));
            bool r = true;
            switch (get_kind(curr)) {
            case object_kind::Constructor:     r = insert_constructor(curr); break;
            case object_kind::Closure:         throw exception("closures cannot be compacted");
            case object_kind::Array:           r = insert_array(curr); break;
            case object_kind::ScalarArray:     copy_object(curr); break;
            case object_kind::String:          copy_object(curr); break;
            case object_kind::MPZ:             insert_mpz(curr); break;
            case object_kind::Thunk:           r = insert_thunk(curr); break;
            case object_kind::Task:            r = insert_task(curr); break;
            case object_kind::Ref:             r = insert_ref(curr); break;
            case object_kind::External:        throw exception("external objects cannot be compacted");
            }
            if (r) m_todo.pop_back();
        }
        m_tmp.clear();
    }
    insert_terminator(o);
}

compacted_region::compacted_region(size_t sz, void * data):
    m_begin(data),
    m_next(data),
    m_end(static_cast<char*>(data)+sz),
    m_nested_mpzs(nullptr) {
}

compacted_region::compacted_region(object_compactor const & c):
    m_begin(malloc(c.size())),
    m_next(m_begin),
    m_end(static_cast<char*>(m_begin) + c.size()),
    m_nested_mpzs(nullptr) {
    memcpy(m_begin, c.data(), c.size());
}

compacted_region::~compacted_region() {
    while (m_nested_mpzs) {
        m_nested_mpzs->m_value.~mpz();
        m_nested_mpzs = *reinterpret_cast<mpz_object**>(reinterpret_cast<char*>(m_nested_mpzs) + sizeof(mpz_object));
    }
    free(m_begin);
}

inline void compacted_region::move(size_t d) {
    lean_assert(m_next < m_end);
    size_t rem = d % sizeof(void*);
    if (rem != 0)
        d = d + sizeof(void*) - rem;
    m_next = static_cast<char*>(m_next) + d;
}

inline object * compacted_region::fix_object_ptr(object * o) {
    if (is_scalar(o)) return o;
    return reinterpret_cast<object*>(static_cast<char*>(m_begin) + reinterpret_cast<size_t>(o));
}

inline void compacted_region::fix_constructor(object * o) {
    object ** it  = cnstr_obj_cptr(o);
    object ** end = it + cnstr_num_objs(o);
    for (; it != end; it++) {
        *it = fix_object_ptr(*it);
    }
    move(cnstr_byte_size(o));
}

inline void compacted_region::fix_array(object * o) {
    object ** it  = array_cptr(o);
    object ** end = it + array_size(o);
    for (; it != end; it++) {
        *it = fix_object_ptr(*it);
    }
    move(array_byte_size(o));
}

inline void compacted_region::fix_thunk(object * o) {
    to_thunk(o)->m_value = fix_object_ptr(to_thunk(o)->m_value);
    move(sizeof(thunk_object));
}

inline void compacted_region::fix_ref(object * o) {
    to_ref(o)->m_value = fix_object_ptr(to_ref(o)->m_value);
    move(sizeof(ref_object));
}

void compacted_region::fix_mpz(object * o) {
    move(sizeof(mpz_object));
    /* convert string after mpz_object into a mpz value */
    std::string s;
    size_t sz = 0;
    char * it = static_cast<char*>(m_next);
    while (*it) {
        s.push_back(*it);
        it++;
        sz++;
    }
    /* use string to initialize memory */
    new (&(to_mpz(o)->m_value)) mpz(s.c_str());
    /* update m_nested_mpzs list */
    *reinterpret_cast<mpz_object**>(m_next) = m_nested_mpzs;
    m_nested_mpzs = to_mpz(o);
    /* consume region after mpz_object */
    sz++; // string delimiter
    if (sz < sizeof(mpz_object*))
        sz = sizeof(mpz_object*);
    move(sz);
}

object * compacted_region::read() {
    if (m_next == m_end)
        return nullptr; /* all objects have been read */
    while (true) {
        lean_assert(static_cast<char*>(m_next) + sizeof(object) <= m_end);
        object * curr = reinterpret_cast<object*>(m_next);
        if (curr->m_kind == TERMINATOR_ID) {
            object * r = reinterpret_cast<terminator_object*>(m_next)->m_value;
            move(sizeof(terminator_object));
            return fix_object_ptr(r);
        } else {
            switch (get_kind(curr)) {
            case object_kind::Constructor:     fix_constructor(curr); break;
            case object_kind::Closure:         lean_unreachable();
            case object_kind::Array:           fix_array(curr); break;
            case object_kind::ScalarArray:     move(sarray_byte_size(curr)); break;
            case object_kind::String:          move(string_byte_size(curr)); break;
            case object_kind::MPZ:             fix_mpz(curr); break;
            case object_kind::Thunk:           fix_thunk(curr); break;
            case object_kind::Ref:             fix_ref(curr); break;
            case object_kind::Task:            lean_unreachable();
            case object_kind::External:        lean_unreachable();
            }
        }
    }
}
}
