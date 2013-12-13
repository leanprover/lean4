/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <algorithm>
#include "util/lua.h"
#include "util/debug.h"
#include "util/name.h"
#include "util/splay_map.h"
#include "util/rc.h"
#include "kernel/expr.h"
#include "library/tactic/assignment.h"

namespace lean {
typedef splay_map<name, expr, name_quick_cmp> proof_map;

/**
   \brief Return the proof for the goal named \c n in the \c proof_map \c m.
   Throw an exception if \c m does not contain a proof for \c n.
*/
expr find(proof_map const & m, name const & n);

/**
   \brief Base class for functors that build a proof for the main goal based on
   the proofs of the subgoals.
*/
class proof_builder_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    proof_builder_cell():m_rc(0) {}
    virtual ~proof_builder_cell() {}
    virtual expr operator()(proof_map const & p, assignment const & a) const = 0;
};

template<typename F>
class proof_builder_tpl : public proof_builder_cell {
    F m_f;
public:
    proof_builder_tpl(F && f):m_f(f) {}
    virtual expr operator()(proof_map const & p, assignment const & a) const { return m_f(p, a); }
};

/**
   \brief Smart pointer for a proof builder functor.
*/
class proof_builder {
protected:
    proof_builder_cell * m_ptr;
public:
    proof_builder():m_ptr(nullptr) {}
    explicit proof_builder(proof_builder_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr); m_ptr->inc_ref(); }
    proof_builder(proof_builder const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    proof_builder(proof_builder && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~proof_builder() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(proof_builder & a, proof_builder & b) { std::swap(a.m_ptr, b.m_ptr); }
    proof_builder & operator=(proof_builder const & s) { LEAN_COPY_REF(s); }
    proof_builder & operator=(proof_builder && s) { LEAN_MOVE_REF(s); }

    expr operator()(proof_map const & p, assignment const & a) const { return m_ptr->operator()(p, a); }
};

template<typename F>
proof_builder mk_proof_builder(F && f) {
    return proof_builder(new proof_builder_tpl<F>(std::forward<F>(f)));
}

proof_builder add_proofs(proof_builder const & pb, list<std::pair<name, expr>> const & prs);

UDATA_DEFS_CORE(proof_map)
UDATA_DEFS(assignment)
UDATA_DEFS(proof_builder)
void open_proof_builder(lua_State * L);
}
