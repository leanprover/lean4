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
typedef std::pair<name, expr> hypothesis;
typedef list<hypothesis>      hypotheses;
class goal {
    hypotheses m_hypotheses;
    expr       m_conclusion;
public:
    goal() {}
    goal(hypotheses const & hs, expr const & c);
    hypotheses const & get_hypotheses() const { return m_hypotheses; }
    expr const & get_conclusion() const { return m_conclusion; }
    format pp(environment const & env, formatter const & fmt, options const & opts) const;
};

inline goal update(goal const & g, expr const & c) { return goal(g.get_hypotheses(), c); }
inline goal update(goal const & g, hypotheses const & hs) { return goal(hs, g.get_conclusion()); }
inline goal update(goal const & g, buffer<hypothesis> const & hs) { return goal(to_list(hs.begin(), hs.end()), g.get_conclusion()); }
inline hypotheses add_hypothesis(name const & h_name, expr const & h, hypotheses const & hs) {
    return cons(mk_pair(h_name, h), hs);
}
inline hypotheses add_hypothesis(hypothesis const & h, hypotheses const & hs) {
    return cons(h, hs);
}

io_state_stream const & operator<<(io_state_stream const & out, goal const & g);

UDATA_DEFS_CORE(hypotheses)
UDATA_DEFS(goal)
void open_goal(lua_State * L);
}
