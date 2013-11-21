/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/debug.h"
#include "util/name.h"
#include "util/splay_map.h"
#include "util/rc.h"
#include "kernel/expr.h"
#include "library/tactic/assignment.h"

namespace lean {
typedef splay_map<name, expr, name_quick_cmp> proof_map;

class proof_builder_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    virtual ~proof_builder_cell() {}
    virtual expr operator()(proof_map const & p, environment const & env, assignment const & a) const = 0;
};

class proof_builder {
protected:
    proof_builder_cell * m_ptr;
public:
    explicit proof_builder(proof_builder_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr); m_ptr->inc_ref(); }
    proof_builder(proof_builder const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    proof_builder(proof_builder && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~proof_builder() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(proof_builder & a, proof_builder & b) { std::swap(a.m_ptr, b.m_ptr); }
    proof_builder & operator=(proof_builder const & s) { LEAN_COPY_REF(proof_builder, s); }
    proof_builder & operator=(proof_builder && s) { LEAN_MOVE_REF(proof_builder, s); }

    expr operator()(proof_map const & p, environment const & env, assignment const & a) const { return m_ptr->operator()(p, env, a); }
};
}
