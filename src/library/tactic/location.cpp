/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/replace_fn.h"
#include "library/kernel_serializer.h"
#include "library/tactic/location.h"

namespace lean {
unsigned occurrence::contains(unsigned occ_idx) const {
    switch (m_kind) {
    case All: return true;
    case Pos: return std::find(m_occs.begin(), m_occs.end(), occ_idx) != m_occs.end();
    case Neg: return std::find(m_occs.begin(), m_occs.end(), occ_idx) == m_occs.end();
    }
    lean_unreachable();
}

serializer & operator<<(serializer & s, occurrence const & o) {
    s << static_cast<char>(o.m_kind);
    write_list<unsigned>(s, o.m_occs);
    return s;
}

deserializer & operator>>(deserializer & d, occurrence & o) {
    o.m_kind = static_cast<occurrence::kind>(d.read_char());
    o.m_occs = read_list<unsigned>(d);
    return d;
}

location location::mk_hypotheses(buffer<name> const & hs) {
    buffer<pair<name, occurrence>> tmp;
    for (name const & h : hs)
        tmp.push_back(mk_pair(h, occurrence()));
    return location(Hypotheses, occurrence(), to_list(tmp));
}

location location::mk_goal_hypotheses(buffer<name> const & hs) {
    buffer<pair<name, occurrence>> tmp;
    for (name const & h : hs)
        tmp.push_back(mk_pair(h, occurrence()));
    return location(GoalHypotheses, occurrence(), to_list(tmp));
}

location location::mk_hypotheses_at(buffer<name> const & hs, buffer<occurrence> const & hs_occs) {
    lean_assert(hs.size() == hs_occs.size());
    buffer<pair<name, occurrence>> tmp;
    for (unsigned i = 0; i < hs.size(); i++)
        tmp.push_back(mk_pair(hs[i], hs_occs[i]));
    return location(Hypotheses, occurrence(), to_list(tmp));
}

location location::mk_at(occurrence const & g_occs, buffer<name> const & hs, buffer<occurrence> const & hs_occs) {
    lean_assert(hs.size() == hs_occs.size());
    buffer<pair<name, occurrence>> tmp;
    for (unsigned i = 0; i < hs.size(); i++)
        tmp.push_back(mk_pair(hs[i], hs_occs[i]));
    return location(GoalHypotheses, g_occs, to_list(tmp));
}

optional<occurrence> location::includes_goal() const {
    switch (m_kind) {
    case Everywhere: case GoalOnly: case GoalHypotheses:
        return optional<occurrence>(m_goal);
    case AllHypotheses: case Hypotheses:
        return optional<occurrence>();
    }
    lean_unreachable();
}

optional<occurrence> location::includes_hypothesis(name const & h) const {
    switch (m_kind) {
    case Everywhere: case AllHypotheses:
        return optional<occurrence>(occurrence());
    case GoalOnly:
        return optional<occurrence>();
    case Hypotheses: case GoalHypotheses:
        for (auto const & p : m_hyps) {
            if (p.first == h)
                return optional<occurrence>(p.second);
        }
        return optional<occurrence>();
    }
    lean_unreachable();
}

void location::get_explicit_hypotheses_names(buffer<name> & r) const {
    for (auto const & p : m_hyps)
        r.push_back(p.first);
}

serializer & operator<<(serializer & s, location const & loc) {
    s << static_cast<char>(loc.m_kind) << loc.m_goal << length(loc.m_hyps);
    for (auto const & p : loc.m_hyps)
        s << p.first << p.second;
    return s;
}

deserializer & operator>>(deserializer & d, location & loc) {
    loc.m_kind = static_cast<location::kind>(d.read_char());
    d >> loc.m_goal;
    unsigned num = d.read_unsigned();
    buffer<pair<name, occurrence>> tmp;
    for (unsigned i = 0; i < num; i++) {
        name h; occurrence o;
        d >> h >> o;
        tmp.emplace_back(h, o);
    }
    loc.m_hyps = to_list(tmp);
    return d;
}

optional<expr> replace_occurrences(expr const & e, expr const & t, occurrence const & occ, unsigned idx) {
    bool use_cache   = occ.is_all();
    unsigned occ_idx = 0;
    bool replaced    =  false;
    expr r = replace(e, [&](expr const & e, unsigned offset) {
            if (e == t) {
                occ_idx++;
                if (occ.contains(occ_idx)) {
                    replaced = true;
                    return some_expr(mk_var(offset+idx));
                }
            }
            return none_expr();
        }, use_cache);
    return replaced ? some_expr(r) : none_expr();
}
}
