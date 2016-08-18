/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/cases_tactic.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"

namespace lean {
// #define trace_match(Code) lean_trace(name({"eqn_compiler", "elim_match"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); Code)
struct elim_match_fn {
    environment     m_env;
    options         m_opts;
    metavar_context m_mctx;

    elim_match_fn(environment const & env, options const & opts,
                  metavar_context const & mctx):
        m_env(env), m_opts(opts), m_mctx(mctx) {}

    struct equation {
        list<pair<name, name>> m_renames;
        local_context          m_lctx;
        list<expr>             m_patterns;
        expr                   m_rhs;
        expr                   m_ref; /* for reporting errors */
        unsigned               m_idx;
    };

    struct program {
        /* Metavariable containing the context for the program */
        expr           m_goal;
        /* Variables that still need to be matched/processed */
        list<name>     m_var_stack;
        list<equation> m_equations;
    };

    type_context mk_type_context(local_context const & lctx) {
        return mk_type_context_for(m_env, m_opts, m_mctx, lctx);
    }

    unsigned get_arity(local_context const & lctx, expr const & e) {
        /* Naive way to retrieve the arity of the function being defined */
        lean_assert(is_equations(e));
        type_context ctx = mk_type_context(lctx);
        unpack_eqns ues(ctx, e);
        return ues.get_arity_of(0);
    }

    pair<expr, list<name>>
    mk_main_goal(local_context lctx, expr fn_type, unsigned arity) {
        type_context ctx = mk_type_context(lctx);
        buffer<name> vars;
        name x("_x");
        for (unsigned i = 0; i < arity; i++) {
            fn_type = ctx.whnf(fn_type);
            if (!is_pi(fn_type)) throw_ill_formed_eqns();
            expr var = ctx.push_local(x.append_after(i+1), binding_domain(fn_type));
            vars.push_back(mlocal_name(var));
            fn_type  = instantiate(binding_body(fn_type), var);
        }
        m_mctx = ctx.mctx();
        expr m = m_mctx.mk_metavar_decl(ctx.lctx(), fn_type);
        return mk_pair(m, to_list(vars));
    }

    optional<equation> mk_equation(local_context const & lctx, expr const & eqn, unsigned idx) {
        expr it = eqn;
        it = binding_body(it); /* consume fn header */
        if (is_no_equation(it)) return optional<equation>();
        type_context ctx = mk_type_context(lctx);
        buffer<expr> locals;
        while (is_lambda(it)) {
            expr type  = instantiate_rev(binding_domain(it), locals);
            expr local = ctx.push_local(binding_name(it), type);
            locals.push_back(local);
            it = binding_body(it);
        }
        lean_assert(is_equation(it));
        equation E;
        E.m_lctx = ctx.lctx();
        E.m_rhs  = instantiate_rev(equation_rhs(it), locals);
        /* The function being defined is not recursive. So, E.m_rhs
           must be closed even if we "consumed" the fn header in
           the beginning of the method. */
        lean_assert(closed(E.m_rhs));
        buffer<expr> patterns;
        get_app_args(equation_lhs(it), patterns);
        for (expr & p : patterns) {
            p = instantiate_rev(p, patterns);
        }
        E.m_patterns = to_list(patterns);
        E.m_ref  = eqn;
        E.m_idx  = idx;
        return optional<equation>(E);
    }

    list<equation> mk_equations(local_context const & lctx, buffer<expr> const & eqns) {
        buffer<equation> R;
        unsigned idx = 0;
        for (expr const & eqn : eqns) {
            if (auto r = mk_equation(lctx, eqn, idx)) {
                R.push_back(*r);
                lean_assert(length(R[0].m_patterns) == length(r->m_patterns));
            } else {
                lean_assert(eqns.size() == 1);
                return list<equation>();
            }
            idx++;
        }
        return to_list(R);
    }

    program mk_program(local_context const & lctx, expr const & e) {
        lean_assert(is_equations(e));
        buffer<expr> eqns;
        to_equations(e, eqns);
        unsigned arity   = get_arity(lctx, e);
        program P;
        expr fn_type  = binding_domain(eqns[0]);
        std::tie(P.m_goal, P.m_var_stack) = mk_main_goal(lctx, fn_type, arity);
        P.m_equations = mk_equations(lctx, eqns);
        return P;
    }

    expr operator()(local_context const & lctx, expr const & eqns) {
        lean_assert(equations_num_fns(eqns) == 1);
        DEBUG_CODE({
                type_context ctx = mk_type_context(lctx);
                lean_assert(!is_recursive_eqns(ctx, eqns));
            });
        program P = mk_program(lctx, eqns);

        lean_unreachable();
    }
};

expr elim_match(environment & env, options const & opts, metavar_context & mctx,
                local_context const & lctx, expr const & eqns) {
    return elim_match_fn(env, opts, mctx)(lctx, eqns);
}

void initialize_elim_match() {
    register_trace_class({"eqn_compiler", "elim_match"});
}
void finalize_elim_match() {
}
}
