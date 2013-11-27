/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/lua.h"
#include "util/debug.h"
#include "util/name.h"
#include "util/rc.h"
#include "util/optional.h"
#include "kernel/expr.h"
#include "kernel/environment.h"
#include "library/tactic/assignment.h"

namespace lean {
/**
   \brief In Lean, a counter-example is encoded using an environment object.
*/
typedef environment counterexample;

/**
   \brief Base class for functors that build a counterexample for the main goal based on
   a counterexample for a subgoal.
*/
class cex_builder_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    cex_builder_cell():m_rc(0) {}
    virtual ~cex_builder_cell() {}
    virtual counterexample operator()(name const & n, optional<counterexample> const & cex, assignment const & a) const = 0;
};

template<typename F>
class cex_builder_tpl : public cex_builder_cell {
    F m_f;
public:
    cex_builder_tpl(F && f):m_f(f) {}
    virtual counterexample operator()(name const & n, optional<counterexample> const & cex, assignment const & a) const {
        return m_f(n, cex, a);
    }
};

/**
   \brief Smart pointer for a counterexample builder functor.
*/
class cex_builder {
protected:
    cex_builder_cell * m_ptr;
public:
    cex_builder():m_ptr(nullptr) {}
    explicit cex_builder(cex_builder_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr); m_ptr->inc_ref(); }
    cex_builder(cex_builder const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    cex_builder(cex_builder && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~cex_builder() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(cex_builder & a, cex_builder & b) { std::swap(a.m_ptr, b.m_ptr); }
    cex_builder & operator=(cex_builder const & s);
    cex_builder & operator=(cex_builder && s);

    counterexample operator()(name const & n, optional<counterexample> const & cex, assignment const & a) const { return m_ptr->operator()(n, cex, a); }
};

template<typename F>
cex_builder mk_cex_builder(F && f) {
    return cex_builder(new cex_builder_tpl<F>(std::forward<F>(f)));
}

UDATA_DEFS(cex_builder)
void open_cex_builder(lua_State * L);
}
