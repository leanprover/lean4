/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "library/blast/state.h"

namespace lean {
namespace blast {
state::state():m_next_mref_index(0) {}

expr state::mk_metavar(hypothesis_idx_buffer const & ctx, expr const & type) {
    hypothesis_idx_set  ctx_as_set;
    for (unsigned const & hidx : ctx)
        ctx_as_set.insert(hidx);
    for_each(type, [&](expr const & e, unsigned) {
            if (!has_href(e))
                return false;
            if (is_href(e)) {
                lean_assert(ctx_as_set.contains(href_index(e)));
                m_main.fix_hypothesis(e);
                return false;
            }
            return true; // continue search
        });
    unsigned idx = m_next_mref_index;
    m_next_mref_index++;
    m_metavar_decls.insert(idx, metavar_decl(to_list(ctx), ctx_as_set, type));
    return blast::mk_mref(idx);
}

expr state::mk_metavar(expr const & type) {
    hypothesis_idx_buffer ctx;
    m_main.get_sorted_hypotheses(ctx);
    return state::mk_metavar(ctx, type);
}

goal state::to_goal(branch const & b) const {
    hypothesis_idx_map<expr> hidx2local;
    metavar_idx_map<expr>    midx2meta;
    name M("M");
    std::function<expr(expr const &)> convert = [&](expr const & e) {
        return lean::replace(e, [&](expr const & e) {
                if (is_href(e)) {
                    auto r = hidx2local.find(href_index(e));
                    lean_assert(r);
                    return some_expr(*r);
                } else if (is_mref(e)) {
                    auto r = midx2meta.find(mref_index(e));
                    if (r) {
                        return some_expr(*r);
                    } else {
                        metavar_decl const * decl = m_metavar_decls.find(mref_index(e));
                        lean_assert(decl);
                        buffer<expr> ctx;
                        for (unsigned hidx : decl->get_context()) {
                            ctx.push_back(*hidx2local.find(hidx));
                        }
                        expr type     = convert(decl->get_type());
                        expr new_type = Pi(ctx, type);
                        expr new_mvar = lean::mk_metavar(name(M, mref_index(e)), new_type);
                        expr new_meta = mk_app(new_mvar, ctx);
                        midx2meta.insert(mref_index(e), new_meta);
                        return some_expr(new_meta);
                    }
                } else {
                    return none_expr();
                }
            });
    };
    name H("H");
    hypothesis_idx_buffer hidxs;
    b.get_sorted_hypotheses(hidxs);
    buffer<expr> hyps;
    for (unsigned hidx : hidxs) {
        hypothesis const * h = b.get(hidx);
        lean_assert(h);
        // after we add support for let-decls in goals, we must convert back h->get_value() if it is available
        expr new_h = lean::mk_local(name(H, hidx), h->get_name(), convert(h->get_type()), binder_info());
        hidx2local.insert(hidx, new_h);
        hyps.push_back(new_h);
    }
    expr new_target    = convert(b.get_target());
    expr new_mvar_type = Pi(hyps, new_target);
    expr new_mvar      = lean::mk_metavar(M, new_mvar_type);
    expr new_meta      = mk_app(new_mvar, hyps);
    return goal(new_meta, new_target);
}

goal state::to_goal() const {
    return to_goal(m_main);
}

void state::display(environment const & env, io_state const & ios) const {
    formatter fmt = ios.get_formatter_factory()(env, ios.get_options());
    ios.get_diagnostic_channel() << mk_pair(to_goal().pp(fmt), ios.get_options());
}

#ifdef LEAN_DEBUG
bool state::check_hypothesis(expr const & e, branch const & b, unsigned hidx, hypothesis const & h) const {
    lean_assert(closed(e));
    for_each(e, [&](expr const & n, unsigned) {
            lean_assert(!blast::is_local(n));
            if (is_href(n)) {
                lean_assert(h.depends_on(n));
                lean_assert(b.hidx_depends_on(hidx, href_index(n)));
            } else if (is_mref(n)) {
                // metavariable is in the set of used metavariables
                lean_assert(b.has_mvar(n));
            }
            return true;
        });
    return true;
}

bool state::check_hypothesis(branch const & b, unsigned hidx, hypothesis const & h) const {
    lean_assert(check_hypothesis(h.get_type(), b, hidx, h));
    lean_assert(!h.get_value() || check_hypothesis(*h.get_value(), b, hidx, h));
    return true;
}

bool state::check_target(branch const & b) const {
    lean_assert(closed(b.get_target()));
    for_each(b.get_target(), [&](expr const & n, unsigned) {
            lean_assert(!blast::is_local(n));
            if (is_href(n)) {
                lean_assert(b.target_depends_on(n));
            } else if (is_mref(n)) {
                // metavariable is in the set of used metavariables
                lean_assert(b.has_mvar(n));
            }
            return true;
        });
    return true;
}

bool state::check_invariant(branch const & b) const {
    b.for_each_hypothesis([&](unsigned hidx, hypothesis const & h) {
            lean_assert(check_hypothesis(b, hidx, h));
        });
    lean_assert(check_target(b));
    return true;
}

bool state::check_invariant() const {
    return check_invariant(m_main);
}
#endif
}}
