/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <algorithm>
#include "util/name_set.h"
#include "util/buffer.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace.h"
#include "kernel/abstract.h"
#include "library/type_inferer.h"
#include "library/tactic/goal.h"

namespace lean {

goal::goal(hypotheses const & hs, expr const & c):m_hypotheses(hs), m_conclusion(c) {}

format goal::pp(formatter const & fmt, options const & opts) const {
    unsigned indent  = get_pp_indent(opts);
    bool unicode     = get_pp_unicode(opts);
    format turnstile = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    buffer<hypothesis> tmp;
    to_buffer(m_hypotheses, tmp);
    bool first = true;
    format r;
    for (auto const & p : tmp) {
        if (first) {
            first = false;
        } else {
            r += compose(comma(), line());
        }
        r += format{format(p.first), space(), colon(), nest(indent, compose(line(), fmt(p.second, opts)))};
    }

    r = group(r);
    r += format{line(), turnstile, space(), nest(indent, fmt(m_conclusion, opts))};
    return group(r);
}

name goal::mk_unique_hypothesis_name(name const & suggestion) const {
    name n = suggestion;
    unsigned i = 0;
    while (true) {
        bool ok = true;
        for (auto const & p : m_hypotheses) {
            if (is_prefix_of(n, p.first)) {
                ok = false;
                break;
            }
        }
        if (ok) {
            return n;
        } else {
            i++;
            n = name(suggestion, i);
        }
    }
}

goal_proof_fn::goal_proof_fn(std::vector<expr> && consts):
    m_constants(consts) {
}

expr goal_proof_fn::operator()(expr const & pr) const {
    return abstract(pr, m_constants.size(), m_constants.data());
}

static name_set collect_used_names(context const & ctx, expr const & t) {
    name_set r;
    auto f = [&r](expr const & e, unsigned) { if (is_constant(e)) r.insert(const_name(e)); return true; };
    for_each_fn<decltype(f)> visitor(f);
    for (auto const & e : ctx) {
        if (expr const & d = e.get_domain())
            visitor(d);
        if (expr const & b = e.get_body())
            visitor(b);
    }
    visitor(t);
    return r;
}

static name mk_unique_name(name_set & s, name const & suggestion) {
    unsigned i = 1;
    name n = suggestion;
    while (true) {
        if (s.find(n) == s.end()) {
            s.insert(n);
            return n;
        } else {
            n = name(suggestion, i);
            i++;
        }
    }
}

std::pair<goal, goal_proof_fn> to_goal(environment const & env, context const & ctx, expr const & t) {
    type_inferer inferer(env);
    if (!inferer.is_proposition(t, ctx))
        throw exception("to goal failed, type is not a proposition");
    name_set used_names = collect_used_names(ctx, t);
    buffer<context_entry> entries;
    for (auto const & e : ctx)
        entries.push_back(e);
    buffer<hypothesis> hypotheses;  // normalized names and types of the entries processed so far
    buffer<expr> bodies;                       // normalized bodies of the entries processed so far
    std::vector<expr> consts;                  // cached consts[i] == mk_constant(names[i], hypotheses[i])
    auto replace_vars = [&](expr const & e, unsigned offset) -> expr {
        if (is_var(e)) {
            unsigned vidx = var_idx(e);
            if (vidx >= offset) {
                unsigned nvidx = vidx - offset;
                unsigned nfv   = consts.size();
                if (nvidx >= nfv)
                    throw exception("to_goal failed, unknown free variable");
                unsigned lvl   = nfv - nvidx - 1;
                if (bodies[lvl])
                    return bodies[lvl];
                else
                    return consts[lvl];
            }
        }
        return e;
    };
    replace_fn<decltype(replace_vars)> replacer(replace_vars);
    auto it    = entries.end();
    auto begin = entries.begin();
    while (it != begin) {
        --it;
        auto const & e = *it;
        name n = mk_unique_name(used_names, e.get_name());
        expr d = replacer(e.get_domain());
        expr b = replacer(e.get_body());
        replacer.clear();
        if (b && (!d || !inferer.is_proposition(d))) {
            hypotheses.emplace_back(n, expr());
            bodies.push_back(b);
            consts.push_back(expr());
        } else {
            hypotheses.emplace_back(n, d);
            bodies.push_back(expr());
            consts.push_back(mk_constant(n, d));
        }
    }
    expr conclusion = replacer(t);
    std::reverse(consts.begin(), consts.end());
    return mk_pair(goal(reverse_to_list(hypotheses.begin(), hypotheses.end()), conclusion),
                   goal_proof_fn(std::move(consts)));
}
}
