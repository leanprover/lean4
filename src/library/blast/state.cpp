/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/blast/state.h"

namespace lean {
namespace blast {
state::state():m_next_mref_index(0) {}

expr state::mk_metavar(hypothesis_idx_buffer const & ctx, expr const & type) {
    hypothesis_idx_set  ctx_as_set;
    for (unsigned const & hidx : ctx)
        ctx_as_set.insert(hidx);
    for_each(type, [&](expr const & e, unsigned) {
            if (!has_lref(e))
                return false;
            if (is_lref(e)) {
                lean_assert(ctx_as_set.contains(lref_index(e)));
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
        return replace(e, [&](expr const & e) {
                if (is_lref(e)) {
                    auto r = hidx2local.find(lref_index(e));
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
        expr new_h = lean::mk_local(h->get_name(), name(H, hidx), convert(h->get_type()), binder_info());
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
}}
