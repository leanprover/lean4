/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <unordered_set>
#include "util/name_generator.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"

namespace lean {
static name * g_elim_dead_let_fresh = nullptr;

class elim_dead_let_fn {
    std::unordered_set<name, name_hash_fn> m_used;
    name_generator                         m_ngen;

    void mark_fvar(expr const & e) {
        m_used.insert(fvar_name(e));
    }

    expr visit_let(expr e) {
        buffer<expr> fvars;
        buffer<expr> lets;
        while (is_let(e)) {
            expr fvar = mk_fvar(m_ngen.next());
            fvars.push_back(fvar);
            lets.push_back(e);
            e = let_body(e);
        }
        e = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        buffer<expr> used;
        buffer<std::tuple<name, expr, expr>> entries;
        while (!fvars.empty()) {
            expr fvar = fvars.back(); fvars.pop_back();
            expr let  = lets.back();  lets.pop_back();
            if (m_used.find(fvar_name(fvar)) != m_used.end()) {
                expr new_type  = visit(instantiate_rev(let_type(let), fvars.size(), fvars.data()));
                expr new_value = visit(instantiate_rev(let_value(let), fvars.size(), fvars.data()));
                used.push_back(fvar);
                entries.emplace_back(let_name(let), new_type, new_value);
            }
        }
        std::reverse(used.begin(), used.end());
        std::reverse(entries.begin(), entries.end());
        e = abstract(e, used.size(), used.data());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr new_type  = abstract(std::get<1>(entries[i]), i, used.data());
            expr new_value = abstract(std::get<2>(entries[i]), i, used.data());
            e = mk_let(std::get<0>(entries[i]), new_type, new_value, e);
        }
        return e;
    }

    expr visit_lambda(expr e) {
        buffer<expr> fvars;
        buffer<std::tuple<name, expr, binder_info>> entries;
        while (is_lambda(e)) {
            expr domain = visit(instantiate_rev(binding_domain(e), fvars.size(), fvars.data()));
            expr fvar   = mk_fvar(m_ngen.next());
            entries.emplace_back(binding_name(e), domain, binding_info(e));
            fvars.push_back(fvar);
            e = binding_body(e);
        }
        e = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        e = abstract(e, fvars.size(), fvars.data());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr new_domain = abstract(std::get<1>(entries[i]), i, fvars.data());
            e = mk_lambda(std::get<0>(entries[i]), new_domain, e, std::get<2>(entries[i]));
        }
        return e;
    }

    expr visit_app(expr const & e) {
        expr fn  = visit(app_fn(e));
        expr arg = visit(app_arg(e));
        return update_app(e, fn, arg);
    }

    expr visit_proj(expr const & e) {
        return update_proj(e, visit(proj_expr(e)));
    }

    expr visit_mdata(expr const & e) {
        return update_mdata(e, visit(mdata_expr(e)));
    }

    expr visit_pi(expr const & e) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_fvar(e))
                    mark_fvar(e);
                return true;
            });
        return e;
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::Proj:   return visit_proj(e);
        case expr_kind::App:    return visit_app(e);
        case expr_kind::FVar:   mark_fvar(e); return e;
        case expr_kind::MData:  return visit_mdata(e);
        case expr_kind::Pi:     return visit_pi(e);
        case expr_kind::Const:  return e;
        case expr_kind::Sort:   return e;
        case expr_kind::Lit:    return e;
        case expr_kind::BVar:   return e;
        case expr_kind::MVar:   lean_unreachable();
        }
        lean_unreachable();
    }

public:
    elim_dead_let_fn():m_ngen(*g_elim_dead_let_fresh) {}

    expr operator()(expr const & e) { return visit(e); }
};

expr elim_dead_let(expr const & e) { return elim_dead_let_fn()(e); }

void initialize_elim_dead_let() {
    g_elim_dead_let_fresh = new name("_elim_dead_let_fresh");
    mark_persistent(g_elim_dead_let_fresh->raw());
    register_name_generator_prefix(*g_elim_dead_let_fresh);
}
void finalize_elim_dead_let() {
    delete g_elim_dead_let_fresh;
}
}
