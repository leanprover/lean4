/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/num.h"
#include "library/string.h"
#include "library/pp_options.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/cases_tactic.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"

namespace lean {
#define trace_match(Code) lean_trace(name({"eqn_compiler", "elim_match"}), Code)

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
        name           m_fn_name; /* for debugging purposes */
        /* Metavariable containing the context for the program */
        expr           m_goal;
        /* Variables that still need to be matched/processed */
        list<name>     m_var_stack;
        list<equation> m_equations;
    };

    type_context mk_type_context(local_context const & lctx) {
        return mk_type_context_for(m_env, m_opts, m_mctx, lctx);
    }

    format nest(format const & fmt) const {
        return ::lean::nest(get_pp_indent(m_opts), fmt);
    }

    unsigned get_arity(local_context const & lctx, expr const & e) {
        /* Naive way to retrieve the arity of the function being defined */
        lean_assert(is_equations(e));
        type_context ctx = mk_type_context(lctx);
        unpack_eqns ues(ctx, e);
        return ues.get_arity_of(0);
    }

    bool is_constructor(expr const & e) const {
        return static_cast<bool>(eqns_env_interface(m_env).is_constructor(e));
    }

    bool is_constructor_app(expr const & e) const {
        return is_constructor(get_app_fn(e));
    }

    bool is_value(expr const & e) const {
        return to_num(e) || to_char(e) || to_string(e) || is_constructor(e);
    }

    expr whnf_pattern(type_context & ctx, expr const & e) {
        return ctx.whnf_pred(e, [&](expr const & e) {
                return !is_constructor_app(e) && !is_value(e);
            });
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
            p = whnf_pattern(ctx, instantiate_rev(p, locals));
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
        P.m_fn_name   = binding_name(eqns[0]);
        expr fn_type  = binding_domain(eqns[0]);
        std::tie(P.m_goal, P.m_var_stack) = mk_main_goal(lctx, fn_type, arity);
        P.m_equations = mk_equations(lctx, eqns);
        return P;
    }

    format pp_equation(equation const & eqn) {
        format r;
        auto pp = mk_pp_ctx(m_env, m_opts, m_mctx, eqn.m_lctx);
        bool first = true;
        for (expr const & p : eqn.m_patterns) {
            if (first) first = false; else r += format(" ");
            r += paren(pp(p));
        }
        r += space() + format(":=") + nest(line() + pp(eqn.m_rhs));
        return group(r);
    }

    format pp_program(program const & P) {
        format r;
        r += format("program") + space() + format(P.m_fn_name);
        metavar_decl mdecl = *m_mctx.get_metavar_decl(P.m_goal);
        local_context lctx = mdecl.get_context();
        auto pp = mk_pp_ctx(m_env, m_opts, m_mctx, lctx);
        format vstack;
        for (name const & x : P.m_var_stack) {
            local_decl x_decl = *lctx.get_local_decl(x);
            vstack += line() + paren(format(x_decl.get_pp_name()) + space() + colon() + space() + pp(x_decl.get_type()));
        }
        r += group(nest(vstack));
        for (equation const & eqn : P.m_equations) {
            r += nest(line() + pp_equation(eqn));
        }
        return r;
    }

    template<typename Pred>
    bool all_next_pattern(program const & P, Pred && p) const {
        for (equation const & eqn : P.m_equations) {
            lean_assert(eqn.m_patterns);
            if (!p(head(eqn.m_patterns)))
                return false;
        }
        return true;
    }

    /* Return true iff the next pattern in all equations is a variable. */
    bool is_variable_transition(program const & P) const {
        return all_next_pattern(P, is_local);
    }

    /* Return true iff the next pattern in all equations is an inaccessible term. */
    bool is_inaccessible_transition(program const & P) const {
        return all_next_pattern(P, is_inaccessible);
    }

    /* Return true iff the next pattern in all equations is a constructor. */
    bool is_constructor_transition(program const & P) const {
        return all_next_pattern(P, [&](expr const & p) { return is_constructor_app(p); });
    }

    /* Return true iff the next pattern of every equation is a constructor or variable,
       and there are at least one equation where it is a variable and another where it is a
       constructor. */
    bool is_complete_transition(program const & P) const {
        bool has_variable    = false;
        bool has_constructor = false;
        bool r = all_next_pattern(P, [&](expr const & p) {
                if (is_local(p)) {
                    has_variable = true; return true;
                } else if (is_constructor_app(p)) {
                    has_constructor = true; return true;
                } else {
                    return false;
                }
            });
        return r && has_variable && has_constructor;
    }

    /* Return true iff the equations are of the form

          v_1 ... := ...
          ...
          v_n ... := ...
          x_1 ... := ...
          ...
          x_m ... := ...

      where v_i's are values and x_j's are variables.
      This transition is used to compile patterns containing
      numerals, characters, strings and enumeration types.
      It is much more efficient than using complete_transition followed by constructor_transition.
      This optimization addresses issue #1089 raised by Jared Roesch. */
    bool is_value_transition(program const & P) const {
        bool found_value = false;
        bool found_var   = false;
        for (equation const & eqn : P.m_equations) {
            lean_assert(eqn.m_patterns);
            expr const & p = head(eqn.m_patterns);
            if (is_value(p)) {
                found_value = true;
                if (found_var) return false;
            } if (is_local(p)) {
                found_var = true;
            } else {
                return false;
            }
        }
        return found_value && found_var;
    }

    expr operator()(local_context const & lctx, expr const & eqns) {
        lean_assert(equations_num_fns(eqns) == 1);
        DEBUG_CODE({
                type_context ctx = mk_type_context(lctx);
                lean_assert(!is_recursive_eqns(ctx, eqns));
            });
        program P = mk_program(lctx, eqns);
        trace_match(tout() << "processing:\n" << pp_program(P) << "\n";);

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
