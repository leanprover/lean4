/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/lua.h"
#include "util/list.h"
#include "util/name.h"
#include "kernel/formatter.h"
#include "kernel/environment.h"
#include "library/io_state_stream.h"

namespace lean {
/**
    \brief A hypothesis is a local variable + a flag indicating whether it is "contextual" or not.
    Only contextual ones are used to build the context of new metavariables.
*/
typedef std::pair<expr, bool> hypothesis;
typedef list<hypothesis>      hypotheses;
class goal {
    hypotheses m_hypotheses;
    expr       m_conclusion;
public:
    goal() {}
    goal(hypotheses const & hs, expr const & c);
    hypotheses const & get_hypotheses() const { return m_hypotheses; }
    expr const & get_conclusion() const { return m_conclusion; }
    /**
        \brief Create a metavarible application <tt>(m l_1 ... l_n)</tt> with type \c type,
        where \c l_1 ... \c l_n are the contextual hypotheses of this goal, and
        \c m is a metavariable with name \c n.
    */
    expr mk_meta(name const & n, expr const & type) const;
    /**
        brief Return true iff this is a valid goal.
        We say a goal is valid when the conclusion only contains local constants that are in hypotheses,
        and each hypothesis only contains local constants that occur in the previous hypotheses.
    */
    bool validate() const;
    goal instantiate_metavars(substitution const & s) const;
    format pp(environment const & env, formatter const & fmt, options const & opts) const;
};

inline goal update(goal const & g, expr const & c) { return goal(g.get_hypotheses(), c); }
inline goal update(goal const & g, hypotheses const & hs) { return goal(hs, g.get_conclusion()); }
inline goal update(goal const & g, buffer<hypothesis> const & hs) { return goal(to_list(hs.begin(), hs.end()), g.get_conclusion()); }
inline hypotheses add_hypothesis(expr const & l, hypotheses const & hs) {
    lean_assert(is_local(l));
    return cons(hypothesis(l, true), hs);
}
inline hypotheses add_hypothesis(hypothesis const & h, hypotheses const & hs) {
    return cons(h, hs);
}

io_state_stream const & operator<<(io_state_stream const & out, goal const & g);

UDATA_DEFS_CORE(hypotheses)
UDATA_DEFS(goal)
void open_goal(lua_State * L);
}
