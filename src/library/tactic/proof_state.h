/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <algorithm>
#include "util/lua.h"
#include "util/rc.h"
#include "util/interrupt.h"
#include "util/optional.h"
#include "util/name_set.h"
#include "library/io_state.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/cex_builder.h"

namespace lean {
typedef list<std::pair<name, goal>> goals;
/**
   \brief Return the name of the i-th goal.

   \remark Return none if i == 0 or i > size(g)
*/
optional<name> get_ith_goal_name(goals const & gs, unsigned i);

enum class precision {
    Precise,
    Under,   // counter-examples can be trusted
    Over,    // proofs can be trusted
    UnderOver // proof_state is garbage: it was produced using under and over approximation steps.
};

precision mk_union(precision p1, precision p2);
bool trust_proof(precision p);
bool trust_cex(precision p);

class proof_state {
    struct cell {
        MK_LEAN_RC();
        precision                   m_precision;
        goals                       m_goals;
        metavar_env                 m_menv;
        proof_builder               m_proof_builder;
        cex_builder                 m_cex_builder;
        void dealloc() { delete this; }
        cell():m_rc(1) {}
        cell(precision prec, goals const & gs, metavar_env const & menv, proof_builder const & p, cex_builder const & c):
            m_rc(1), m_precision(prec), m_goals(gs), m_menv(menv), m_proof_builder(p), m_cex_builder(c) {}
        cell(goals const & gs, metavar_env const & menv, proof_builder const & p, cex_builder const & c):
            m_rc(1), m_precision(precision::Precise), m_goals(gs), m_menv(menv), m_proof_builder(p), m_cex_builder(c) {}
    };
    cell * m_ptr;
public:
    proof_state():m_ptr(new cell()) {}
    proof_state(proof_state const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    proof_state(proof_state && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    proof_state(goals const & gs, metavar_env const & menv, proof_builder const & p, cex_builder const & c):
        m_ptr(new cell(gs, menv, p, c)) {}
    proof_state(precision prec, goals const & gs, metavar_env const & menv, proof_builder const & p, cex_builder const & c):
        m_ptr(new cell(prec, gs, menv, p, c)) {}
    proof_state(proof_state const & s, goals const & gs, proof_builder const & p):
        m_ptr(new cell(s.get_precision(), gs, s.get_menv(), p, s.get_cex_builder())) {}
    proof_state(proof_state const & s, goals const & gs):
        m_ptr(new cell(s.get_precision(), gs, s.get_menv(), s.get_proof_builder(), s.get_cex_builder())) {}
    proof_state(proof_state const & s, goals const & gs, proof_builder const & p, cex_builder const & c):
        m_ptr(new cell(s.get_precision(), gs, s.get_menv(), p, c)) {}
    ~proof_state() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(proof_state & a, proof_state & b) { std::swap(a.m_ptr, b.m_ptr); }
    proof_state & operator=(proof_state const & s) { LEAN_COPY_REF(s); }
    proof_state & operator=(proof_state && s) { LEAN_MOVE_REF(s); }
    precision get_precision() const { lean_assert(m_ptr); return m_ptr->m_precision; }
    goals const & get_goals() const { lean_assert(m_ptr); return m_ptr->m_goals; }
    metavar_env const & get_menv() const { lean_assert(m_ptr); return m_ptr->m_menv; }
    proof_builder const & get_proof_builder() const { lean_assert(m_ptr); return m_ptr->m_proof_builder; }
    cex_builder const & get_cex_builder() const { lean_assert(m_ptr); return m_ptr->m_cex_builder; }
    /**
        \brief Return true iff this state does not have any goals left, and
        the precision is \c Precise or \c Over
    */
    bool is_proof_final_state() const;
    /**
       \brief Return true iff this state has only one goal of the form <tt> |- false</tt>,
       and the precision is \c Precise or \c Under
    */
    bool is_cex_final_state() const;
    /**
       \brief Store in \c r the goal names
    */
    void get_goal_names(name_set & r) const;

    optional<name> get_ith_goal_name(unsigned i) const { return ::lean::get_ith_goal_name(get_goals(), i); }

    format pp(formatter const & fmt, options const & opts) const;
};

proof_state to_proof_state(ro_environment const & env, context const & ctx, expr const & t);

inline optional<proof_state> some_proof_state(proof_state const & s, goals const & gs, proof_builder const & p) {
    return some(proof_state(s, gs, p));
}
inline optional<proof_state> none_proof_state() { return optional<proof_state> (); }

template<typename F>
goals map_goals(proof_state const & s, F && f) {
    return map_filter(s.get_goals(), [=](std::pair<name, goal> const & in, std::pair<name, goal> & out) -> bool {
            check_interrupted();
            optional<goal> new_goal = f(in.first, in.second);
            if (new_goal) {
                out.first  = in.first;
                out.second = *new_goal;
                return true;
            } else {
                return false;
            }
        });
}

io_state_stream const & operator<<(io_state_stream const & out, proof_state & s);

UDATA_DEFS_CORE(goals)
UDATA_DEFS(proof_state)
void open_proof_state(lua_State * L);
}
