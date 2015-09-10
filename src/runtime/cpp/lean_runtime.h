/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/thread.h"
#include <vector>
#include <gmp.h>

namespace lean {
class obj;
enum class obj_kind { Constructor, Closure, MPN };

class obj_cell {
    atomic<unsigned> m_rc;
    unsigned m_kind:2;
    unsigned m_size:14;
    unsigned m_cidx:16; // constructor idx if Constructor, and arity if closure
    bool dec_ref_core() {
        if (atomic_fetch_sub_explicit(&m_rc, 1u, memory_order_release) == 1u) {
            atomic_thread_fence(memory_order_acquire);
            return true;
        } else {
            return false;
        }
    }
    void dealloc();
    obj_cell(unsigned cidx, unsigned sz, obj const * fs);
    obj_cell(void * fn, unsigned arity, unsigned sz, obj const * fs);
    friend obj mk_obj(unsigned cidx, unsigned n, obj const * fs);
    friend obj mk_closure_core(void * fn, unsigned arity, unsigned n, obj const * fs);
    void ** field_addr() {
        return reinterpret_cast<void **>(reinterpret_cast<char*>(this)+sizeof(obj_cell));
    }
    void ** fn_ptr_addr() { return field_addr() + m_size; }
    void copy_fields(obj_cell const & src);
public:
    obj_cell(obj_cell const & src, obj const & a1);
    obj_cell(obj_cell const & src, obj const & a1, obj const & a2);
    obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3);
    obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4);
    obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5);
    obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5,
             obj const & a6);
    obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5,
             obj const & a6, obj const & a7);
    obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5,
             obj const & a6, obj const & a7, obj const & a8);
    unsigned get_rc() const { return atomic_load(&m_rc); }
    void inc_ref() { atomic_fetch_add_explicit(&m_rc, 1u, memory_order_relaxed); }
    void dec_ref() { if (dec_ref_core()) { dealloc(); } }
    obj_kind kind() const { return static_cast<obj_kind>(m_kind); }
    size_t cidx() const { return m_cidx; }
    unsigned size() const { return m_size; }
    unsigned arity() const { return m_cidx; }
    obj const * field_ptr() const {
        return reinterpret_cast<obj const *>(reinterpret_cast<char const *>(this)+sizeof(obj_cell));
    }
    void * fn_ptr() const {
        return *(reinterpret_cast<void **>(const_cast<obj*>(field_ptr()))+m_size);
    }
};

#define LEAN_IS_PTR(obj) ((reinterpret_cast<size_t>(obj) & 1) == 0)
#define LEAN_BOX(num)    (reinterpret_cast<obj_cell*>((num << 1) | 1))
#define LEAN_UNBOX(obj)  (reinterpret_cast<size_t>(obj) >> 1)

class obj {
    friend class obj_cell;
    obj_cell * m_data;
    void copy_fields(std::vector<obj> & r);
    obj apply() const;
    obj_cell * steal_ptr() { obj_cell * r = m_data; m_data = LEAN_BOX(0); return r; }
public:
    obj():m_data(LEAN_BOX(0)) { static_assert(sizeof(obj) == sizeof(void *), "unexpected class obj size"); } // NOLINT
    obj(unsigned cidx):m_data(LEAN_BOX(cidx)) {}
    obj(obj_cell * c):m_data(c) { m_data->inc_ref(); }
    obj(obj const & o):m_data(o.m_data) { if (LEAN_IS_PTR(m_data)) m_data->inc_ref(); }
    obj(obj && o):m_data(o.m_data) { o.m_data = LEAN_BOX(0); }
    ~obj() { if (LEAN_IS_PTR(m_data)) m_data->dec_ref(); }

    obj & operator=(obj const & s) {
        if (LEAN_IS_PTR(s.m_data))
            s.m_data->inc_ref();
        auto new_data = s.m_data;
        if (LEAN_IS_PTR(m_data))
            m_data->dec_ref();
        m_data = new_data;
        return *this;
    }

    obj & operator=(obj && s) {
        if (LEAN_IS_PTR(m_data))
            m_data->dec_ref();
        m_data   = s.m_data;
        s.m_data = LEAN_BOX(0);
        return *this;
    }

    obj_cell const & data() const { return *m_data; }
    size_t cidx() const { return LEAN_IS_PTR(m_data) ? m_data->cidx() : LEAN_UNBOX(m_data); }
    unsigned size() const { return m_data->size(); }
    obj const & fld(unsigned fidx) const { return m_data->field_ptr()[fidx]; }
    obj const & operator[](unsigned fidx) const { return fld(fidx); }

    unsigned arity() const { return m_data->arity(); }
    void * fn_ptr() const { return m_data->fn_ptr(); }

    obj apply(obj const &) const;
    obj apply(obj const &, obj const &) const;
    obj apply(obj const &, obj const &, obj const &) const;
    obj apply(obj const &, obj const &, obj const &, obj const &) const;
    obj apply(obj const &, obj const &, obj const &, obj const &, obj const &) const;
    obj apply(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &) const;
    obj apply(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
              obj const &) const;
    obj apply(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
              obj const &, obj const &) const;
    obj apply(unsigned, obj const *) const;
};

inline obj mk_obj(unsigned cidx) { return obj(cidx); }
obj mk_obj(unsigned cidx, unsigned n, obj const * fs);
inline obj mk_obj(unsigned cidx, obj const & o) { return mk_obj(cidx, 1, &o); }
inline obj mk_obj(unsigned cidx, std::initializer_list<obj> const & os) { return mk_obj(cidx, os.size(), os.begin()); }

obj mk_closure_core(void * fn, unsigned arity, unsigned n, obj const * fs);
template<typename T>
obj mk_closure(T fn, unsigned arity, unsigned n, obj const * fs) {
    return mk_closure_core(reinterpret_cast<void*>(fn), arity, n, fs);
}
template<typename T>
obj mk_closure(T fn, unsigned arity, std::initializer_list<obj> const & os) {
    return mk_closure_core(reinterpret_cast<void*>(fn), arity, os.size(), os.begin());
}
}
