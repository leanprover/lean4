/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "library/compiler/lc_util.h"

namespace lean {
static name * g_cse_fresh = nullptr;

class cse_fn {
    environment       m_env;
    name_generator    m_ngen;
    expr_map<expr>    m_lval2fvar;
    std::vector<expr> m_lvals;
public:

    expr visit_let(expr e) {
        unsigned lvals_size = m_lvals.size();
        buffer<expr> fvars;
        buffer<expr> to_keep_fvars;
        buffer<std::tuple<name, expr, expr>> entries;
        while (is_let(e)) {
            expr value = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            auto it    = m_lval2fvar.find(value);
            if (it != m_lval2fvar.end()) {
                lean_assert(is_fvar(it->second));
                fvars.push_back(it->second);
            } else {
                expr type      = instantiate_rev(let_type(e), fvars.size(), fvars.data());
                expr new_value = visit_let_value(value);
                expr fvar      = mk_fvar(m_ngen.next());
                fvars.push_back(fvar);
                to_keep_fvars.push_back(fvar);
                entries.emplace_back(let_name(e), type, new_value);
                if (!is_cases_on_app(m_env, new_value)) {
                    m_lval2fvar.insert(mk_pair(new_value, fvar));
                    m_lvals.push_back(new_value);
                }
            }
            e = let_body(e);
        }
        e = instantiate_rev(e, fvars.size(), fvars.data());
        e = abstract(e, to_keep_fvars.size(), to_keep_fvars.data());
        lean_assert(entries.size() == to_keep_fvars.size());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr new_type  = abstract(std::get<1>(entries[i]), i, to_keep_fvars.data());
            expr new_value = abstract(std::get<2>(entries[i]), i, to_keep_fvars.data());
            e = mk_let(std::get<0>(entries[i]), new_type, new_value, e);
        }
        /* Restore m_lval2fvar */
        for (unsigned i = lvals_size; i < m_lvals.size(); i++) {
            m_lval2fvar.erase(m_lvals[i]);
        }
        m_lvals.resize(lvals_size);
        return e;
    }

    expr visit_lambda(expr e) {
        buffer<expr> fvars;
        buffer<std::tuple<name, expr, binder_info>> entries;
        while (is_lambda(e)) {
            expr domain = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
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
        if (is_cases_on_app(m_env, e)) {
            buffer<expr> args;
            expr const & c = get_app_args(e, args);
            lean_assert(is_constant(c));
            inductive_val I_val      = m_env.get(const_name(c).get_prefix()).to_inductive_val();
            unsigned first_minor_idx = I_val.get_nparams() + 1 /* typeformer/motive */ + I_val.get_nindices() + 1;
            for (unsigned i = first_minor_idx; i < args.size(); i++) {

                args[i] = visit(args[i]);
            }
            return mk_app(c, args);
        } else {
            return e;
        }
    }

    expr visit_let_value(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::App:    return visit_app(e);
        default:                return e;
        }
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    cse_fn(environment const & env):
        m_env(env), m_ngen(*g_cse_fresh) {
    }

    expr operator()(expr const & e) { return visit(e); }
};

expr cse(environment const & env, expr const & e) {
    return cse_fn(env)(e);
}

void initialize_cse() {
    g_cse_fresh = new name("_cse_fresh");
    register_name_generator_prefix(*g_cse_fresh);
}
void finalize_cse() {
    delete g_cse_fresh;
}
}
