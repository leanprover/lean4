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
/*
  Special object that terminates the data block constructing the object graph rooted in `m_value`.
  We use this object to ensure `m_value` is correctly aligned. In the past, we would allocate
  a chunk of memory `p` of size `sizeof(object) + sizeof(object*)`, and then write at `p + sizeof(object)`.
  This is incorrect because `sizeof(object)` is not a multiple of the word size.
*/
struct terminator_object {
    lean_object   m_header;
    lean_object * m_value;
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
    if (lean_is_scalar(o)) {
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
    size_t sz = sizeof(terminator_object);
    terminator_object * t = (terminator_object*) alloc(sz);
    lean_set_non_heap_header((lean_object*)t, sz, LeanReserved, 0);
    t->m_value = to_offset(o);
}

object * object_compactor::copy_object(object * o) {
    size_t sz  = lean_object_byte_size(o);
    void * mem = alloc(sz);
    memcpy(mem, o, sz);
    object * r = static_cast<object*>(mem);
    lean_set_non_heap_header(r, sz, lean_ptr_tag(o), lean_ptr_other(o));
    lean_assert(!lean_has_rc(r));
    lean_assert(lean_ptr_tag(r) == lean_ptr_tag(o));
    lean_assert(lean_ptr_other(r) == lean_ptr_other(o));
    lean_assert(lean_object_byte_size(r) == sz);
    save(o, r);
    return r;
}

bool object_compactor::insert_constructor(object * o) {
    std::vector<object_offset> & offsets = m_tmp;
    offsets.clear();
    bool missing_children = false;
    unsigned num_objs     = lean_ctor_num_objs(o);
    for (unsigned i = 0; i < num_objs; i++) {
        object_offset c = to_offset(cnstr_get(o, i));
        if (c == g_null_offset)
            missing_children = true;
        offsets.push_back(c);
    }
    if (missing_children)
        return false;
    object * new_o = copy_object(o);
    for (unsigned i = 0; i < lean_ctor_num_objs(o); i++)
        lean_ctor_set(new_o, i, offsets[i]);
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
    size_t obj_sz = sizeof(lean_array_object) + sizeof(void*)*sz;
    lean_array_object * new_o = (lean_array_object*)alloc(obj_sz);
    lean_set_non_heap_header((lean_object*)new_o, obj_sz, LeanArray, 0);
    new_o->m_size     = sz;
    new_o->m_capacity = sz;
    for (size_t i = 0; i < sz; i++) {
        lean_array_set_core((lean_object*)new_o, i, offsets[i]);
    }
    save(o, (lean_object*)new_o);
    return true;
}

bool object_compactor::insert_thunk(object * o) {
    object * v = lean_thunk_get(o);
    object_offset c = to_offset(v);
    if (c == g_null_offset)
        return false;
    object * r = copy_object(o);
    lean_to_thunk(r)->m_value = c;
    return true;
}

bool object_compactor::insert_ref(object * o) {
    object * v = lean_to_ref(o)->m_value;
    object_offset c = to_offset(v);
    if (c == g_null_offset)
        return false;
    object * r = copy_object(o);
    lean_to_ref(r)->m_value = c;
    return true;
}

bool object_compactor::insert_task(object * o) {
    object * v = lean_task_get(o);
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
    size_t sz = sizeof(lean_thunk_object);
    lean_thunk_object * new_o = (lean_thunk_object*)alloc(sz);
    lean_set_non_heap_header((lean_object*)new_o, sz, LeanThunk, 0);
    new_o->m_value   = c;
    new_o->m_closure = (lean_object*)0;
    save(o, (lean_object*)new_o);
    return true;
}

void object_compactor::insert_mpz(object * o) {
    std::string s       = mpz_value(o).to_string();
    /* Remark: in the compacted_region object, we use the space after the mpz_object
       to store the next mpz_object in the region AFTER we convert the string back
       into an mpz number. So, we use std::max to make sure we have enough space for both. */
    size_t extra_space  = std::max(s.size() + 1, sizeof(mpz_object*));
    size_t sz      = sizeof(mpz_object) + extra_space;
    void * mem     = alloc(sz);
    mpz_object * new_o = new (mem) mpz_object();
    lean_set_non_heap_header((lean_object*)new_o, sz, LeanMPZ, 0);
    save(o, (lean_object*)new_o);
    void * data    = reinterpret_cast<char*>(new_o) + sizeof(mpz_object);
    memcpy(data, s.c_str(), s.size() + 1);
}

void object_compactor::operator()(object * o) {
    lean_assert(m_todo.empty());
    if (!lean_is_scalar(o)) {
        m_todo.push_back(o);
        while (!m_todo.empty()) {
            object * curr = m_todo.back();
            if (m_obj_table.find(curr) != m_obj_table.end()) {
                m_todo.pop_back();
                continue;
            }
            lean_assert(!lean_is_scalar(curr));
            bool r = true;
            switch (lean_ptr_tag(curr)) {
            case LeanClosure:         lean_panic("closures cannot be compacted");
            case LeanArray:           r = insert_array(curr); break;
            case LeanScalarArray:     copy_object(curr); break;
            case LeanString:          copy_object(curr); break;
            case LeanMPZ:             insert_mpz(curr); break;
            case LeanThunk:           r = insert_thunk(curr); break;
            case LeanTask:            r = insert_task(curr); break;
            case LeanRef:             r = insert_ref(curr); break;
            case LeanExternal:        lean_panic("external objects cannot be compacted");
            case LeanReserved:        lean_unreachable();
            default:                  r = insert_constructor(curr); break;
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

inline object * compacted_region::fix_object_ptr(object * o) {
    if (lean_is_scalar(o)) return o;
    return reinterpret_cast<object*>(static_cast<char*>(m_begin) + reinterpret_cast<size_t>(o));
}

inline void compacted_region::move(size_t d) {
    lean_assert(m_next < m_end);
    size_t rem = d % sizeof(void*);
    if (rem != 0)
        d = d + sizeof(void*) - rem;
    m_next = static_cast<char*>(m_next) + d;
}

inline void compacted_region::move(object * o) {
    return move(lean_object_byte_size(o));
}

inline void compacted_region::fix_constructor(object * o) {
    lean_assert(!lean_has_rc(o));
    object ** it  = lean_ctor_obj_cptr(o);
    object ** end = it + lean_ctor_num_objs(o);
    for (; it != end; it++) {
        *it = fix_object_ptr(*it);
    }
    lean_assert(lean_object_byte_size(o) < 4192);
    move(o);
}

inline void compacted_region::fix_array(object * o) {
    object ** it  = lean_array_cptr(o);
    object ** end = it + lean_array_size(o);
    for (; it != end; it++) {
        *it = fix_object_ptr(*it);
    }
    move(o);
}

inline void compacted_region::fix_thunk(object * o) {
    lean_to_thunk(o)->m_value = fix_object_ptr(lean_to_thunk(o)->m_value);
    move(sizeof(lean_thunk_object));
}

inline void compacted_region::fix_ref(object * o) {
    lean_to_ref(o)->m_value = fix_object_ptr(lean_to_ref(o)->m_value);
    move(sizeof(lean_ref_object));
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
    new (&(((mpz_object*)o)->m_value)) mpz(s.c_str()); // NOLINT
    /* update m_nested_mpzs list */
    *reinterpret_cast<mpz_object**>(m_next) = m_nested_mpzs;
    m_nested_mpzs = (mpz_object*)o;
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
        uint8 tag = lean_ptr_tag(curr);
        if (tag <= LeanMaxCtorTag) {
            fix_constructor(curr);
        } else {
            switch (tag) {
            case LeanClosure:         lean_unreachable();
            case LeanArray:           fix_array(curr); break;
            case LeanScalarArray:     move(lean_sarray_byte_size(curr)); break;
            case LeanString:          move(lean_string_byte_size(curr)); break;
            case LeanMPZ:             fix_mpz(curr); break;
            case LeanThunk:           fix_thunk(curr); break;
            case LeanRef:             fix_ref(curr); break;
            case LeanTask:            lean_unreachable();
            case LeanExternal:        lean_unreachable();
            case LeanReserved: {
                object * r = reinterpret_cast<terminator_object*>(m_next)->m_value;
                move(sizeof(terminator_object));
                return fix_object_ptr(r);
            }
            default:                  lean_unreachable();
            }
        }
    }
}
}
