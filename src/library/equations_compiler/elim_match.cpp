/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/flet.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "library/placeholder.h"
#include "kernel/inductive/inductive.h"
#include "library/max_sharing.h"
#include "library/trace.h"
#include "library/num.h"
#include "library/constants.h"
#include "library/idx_metavar.h"
#include "library/string.h"
#include "library/pp_options.h"
#include "library/exception.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/annotation.h"
#include "library/private.h"
#include "library/inverse.h"
#include "library/aux_definition.h"
#include "library/app_builder.h"
#include "library/sorry.h"
#include "library/delayed_abstraction.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/cases_tactic.h"
#include "library/tactic/intro_tactic.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/elim_match.h"
#include "frontends/lean/elaborator.h"

#ifndef LEAN_DEFAULT_EQN_COMPILER_ITE
#define LEAN_DEFAULT_EQN_COMPILER_ITE true
#endif

#ifndef LEAN_DEFAULT_EQN_COMPILER_MAX_STEPS
#define LEAN_DEFAULT_EQN_COMPILER_MAX_STEPS 2048
#endif

namespace lean {
static name * g_eqn_compiler_ite       = nullptr;
static name * g_eqn_compiler_max_steps = nullptr;

static bool get_eqn_compiler_ite(options const & o) {
    return o.get_bool(*g_eqn_compiler_ite, LEAN_DEFAULT_EQN_COMPILER_ITE);
}

static unsigned get_eqn_compiler_max_steps(options const & o) {
    return o.get_unsigned(*g_eqn_compiler_max_steps, LEAN_DEFAULT_EQN_COMPILER_MAX_STEPS);
}

#define trace_match(Code) lean_trace(name({"eqn_compiler", "elim_match"}), Code)
#define trace_match_debug(Code) lean_trace(name({"debug", "eqn_compiler", "elim_match"}), Code)

struct elim_match_fn {
    environment     m_env;
    elaborator &    m_elab;
    metavar_context m_mctx;

    expr            m_ref;
    unsigned        m_depth{0};
    buffer<bool>    m_used_eqns;
    bool            m_aux_lemmas;
    unsigned        m_num_steps{0};

    bool m_error_during_process = false;

    /* configuration options */
    bool            m_use_ite;
    unsigned        m_max_steps;

    /* m_enum is a mapping from inductive type name to flag indicating whether it is
       an enumeration type or not. */
    name_map<bool>  m_enum;

    elim_match_fn(environment const & env, elaborator & elab,
                  metavar_context const & mctx):
        m_env(env), m_elab(elab), m_mctx(mctx) {
        m_use_ite   = get_eqn_compiler_ite(elab.get_options());
        m_max_steps = get_eqn_compiler_max_steps(elab.get_options());
    }

    struct equation {
        local_context  m_lctx;
        list<expr>     m_patterns;
        expr           m_rhs;
        /* m_renames map variables in this->m_lctx to problem local context */
        hsubstitution  m_subst;
        expr           m_ref; /* for producing error messages */
        unsigned       m_eqn_idx; /* for producing error message */
        /* The following fields are only used for lemma generation */
        list<expr>     m_hs;
        list<expr>     m_vars;
        list<expr>     m_lhs_args;
    };

    struct problem {
        name           m_fn_name;
        expr           m_goal;
        list<expr>     m_var_stack;
        list<equation> m_equations;
        list<expr>     m_example;
    };

    buffer<problem> m_unsolved;

    struct lemma {
        local_context  m_lctx;
        list<expr>     m_vars;
        list<expr>     m_hs;
        list<expr>     m_lhs_args;
        expr           m_rhs;
        unsigned       m_eqn_idx;
    };

    [[ noreturn ]] void throw_error(char const * msg) {
        throw generic_exception(m_ref, msg);
    }

    [[ noreturn ]] void throw_error(sstream const & strm) {
        throw generic_exception(m_ref, strm);
    }

    local_context get_local_context(expr const & mvar) {
        return m_mctx.get_metavar_decl(mvar).get_context();
    }

    local_context get_local_context(problem const & P) {
        return get_local_context(P.m_goal);
    }

    /* (for debugging, i.e., writing assertions) make sure all locals
       in `e` are defined in `lctx` */
    bool check_locals_decl_at(expr const & e, local_context const & lctx) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_local(e) && !lctx.find_local_decl(e)) {
                    lean_unreachable();
                }
                return true;
            });
        return true;
    }

    /* For debugging */
    bool check_equation(problem const & P, equation const & eqn) {
        lean_assert(length(eqn.m_patterns) == length(P.m_var_stack));
        local_context const & lctx = get_local_context(P);
        eqn.m_subst.for_each([&](name const & n, expr const & e) {
                if (!eqn.m_lctx.find_local_decl(n)) {
                    lean_unreachable();
                }
                if (!check_locals_decl_at(e, lctx)) {
                    lean_unreachable();
                }
            });
        lean_assert(check_locals_decl_at(eqn.m_rhs, eqn.m_lctx));
        for (expr const & p : eqn.m_patterns) {
            if (!check_locals_decl_at(p, eqn.m_lctx)) {
                lean_unreachable();
            }
        }
        return true;
    }

    /* For debugging */
    bool check_problem(problem const & P) {
        local_context const & lctx = get_local_context(P);
        for (expr const & x : P.m_var_stack) {
            if (!check_locals_decl_at(x, lctx)) {
                lean_unreachable();
            }
        }
        for (equation const & eqn : P.m_equations) {
            if (!check_equation(P, eqn)) {
                lean_unreachable();
            }
        }
        auto tc = mk_type_context(P);
        return true;
    }

    type_context_old mk_type_context(local_context const & lctx) {
        return type_context_old(m_env, m_mctx, lctx, m_elab.get_cache(), transparency_mode::Semireducible);
    }

    type_context_old mk_type_context(expr const & mvar) {
        return mk_type_context(get_local_context(mvar));
    }

    type_context_old mk_type_context(problem const & P) {
        return mk_type_context(get_local_context(P));
    }

    options const & get_options() const { return m_elab.get_options(); }

    std::function<format(expr const &)> mk_pp_ctx(local_context const & lctx) {
        options opts = get_options();
        opts = opts.update(get_pp_beta_name(), false);
        type_context_old ctx = mk_type_context(lctx);
        return ::lean::mk_pp_ctx(ctx);
    }

    std::function<format(expr const &)> mk_pp_ctx(problem const & P) {
        return mk_pp_ctx(get_local_context(P));
    }

    format nest(format const & fmt) const {
        return ::lean::nest(get_pp_indent(get_options()), fmt);
    }

    format pp_equation(equation const & eqn) {
        format r;
        auto pp = mk_pp_ctx(eqn.m_lctx);
        bool first = true;
        for (expr const & p : eqn.m_patterns) {
            if (first) first = false; else r += format(" ");
            r += paren(pp(p));
        }
        r += space() + format(":=") + nest(line() + pp(eqn.m_rhs));
        return group(r);
    }

    format pp_problem(problem const & P) {
        format r;
        auto pp = mk_pp_ctx(P);
        type_context_old ctx = mk_type_context(P);
        r += format("match") + space() + format(P.m_fn_name) + space() + format(":") + space() + pp(ctx.infer(P.m_goal));
        format v;
        bool first = true;
        for (expr const & x : P.m_var_stack) {
            if (first) first = false; else v += comma() + space();
            v += pp(x);
        }
        r += bracket("[", v, "]");
        for (equation const & eqn : P.m_equations) {
            r += nest(line() + pp_equation(eqn));
        }

        auto example = format("example:");
        for (auto & ex : P.m_example) {
            example += space() + paren(pp(ex));
        }
        r += line() + nest(example);

        return r;
    }

    optional<name> is_constructor(name const & n) const {
        return is_ginductive_intro_rule(m_env, n);
    }
    optional<name> is_constructor(expr const & e) const {
        if (!is_constant(e)) return optional<name>();
        return is_constructor(const_name(e));
    }
    optional<name> is_constructor_app(type_context_old & ctx, expr const & e) const {
        if (auto ind_type = is_constructor(get_app_fn(e))) {
            // Check that e is not a partially applied constructor.
            auto e_type = whnf_ginductive(ctx, ctx.infer(e));
            if (is_app_of(e_type, *ind_type)){
                return ind_type;
            }
        }
        return optional<name>();
    }

    bool is_inductive(name const & n) const { return static_cast<bool>(is_ginductive(m_env, n)); }
    bool is_inductive(expr const & e) const { return is_constant(e) && is_inductive(const_name(e)); }
    bool is_inductive_app(expr const & e) const { return is_inductive(get_app_fn(e)); }

    void get_constructors_of(name const & n, buffer<name> & c_names) const {
        lean_assert(is_inductive(n));
        to_buffer(get_ginductive_intro_rules(m_env, n), c_names);
    }

    /* Return true iff `e` is of the form (I.below ...) or (I.ibelow ...) where `I` is an inductive datatype.
       Move to a different module? */
    bool is_below_type(expr const & e) const {
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn)) return false;
        name const & fn_name = const_name(fn);
        if (fn_name.is_atomic() || !fn_name.is_string()) return false;
        std::string s(fn_name.get_string());
        return is_inductive(fn_name.get_prefix()) && (s == "below" || s == "ibelow");
    }

    /* Return true iff I_name is an enumeration type with more than 2 elements.

       \remark It is not worth to apply the if-then-else compilation step if the enumeration
       types has only 2 (or 1) element. */
    bool is_nontrivial_enum(name const & I_name) {
        if (auto r = m_enum.find(I_name))
            return *r;
        buffer<name> c_names;
        get_constructors_of(I_name, c_names);
        bool result = true;
        if (c_names.size() <= 2) {
            result = false;
        } else {
            for (name const & c_name : c_names) {
                declaration d = m_env.get(c_name);
                expr type = d.get_type();
                if (!is_constant(type) || const_name(type) != I_name) {
                    result = false;
                    break;
                }
            }
        }
        m_enum.insert(I_name, result);
        return result;
    }

    bool is_value(type_context_old & ctx, expr const & e) {
        try {
            if (!m_use_ite) return false;
            if (is_nat_int_char_string_name_value(ctx, e)) return true;
            // TODO(Leo, Sebastian): decide whether we ever want to have this behavior back
            // if (optional<name> I_name = is_constructor(e)) return is_nontrivial_enum(*I_name);
            return false;
        } catch (exception &) {
            lean_unreachable();
        }
    }

    bool is_finite_value(type_context_old & ctx, expr const & e) {
        lean_assert(is_value(ctx, e));
        return is_char_value(ctx, e);
    }

    bool is_transport_app(expr const & e) {
        if (!is_app(e)) return false;
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn)) return false;
        optional<inverse_info> info = has_inverse(m_env, const_name(fn));
        if (!info || info->m_arity != get_app_num_args(e)) return false;
        optional<inverse_info> inv_info = has_inverse(m_env, info->m_inv);
        return
            inv_info &&
            info->m_arity == inv_info->m_inv_arity &&
            inv_info->m_arity == info->m_inv_arity;
    }

    unsigned get_inductive_num_params(name const & n) const { return get_ginductive_num_params(m_env, n); }
    unsigned get_inductive_num_params(expr const & I) const { return get_inductive_num_params(const_name(I)); }

    /* Normalize until head is constructor or value */
    expr whnf_pattern(type_context_old & ctx, expr const & e) {
        if (is_inaccessible(e)) {
            return e;
        } else if (is_value(ctx, e)) {
            return e;
        } else {
            /* The case is_value(ctx, e) above is needed because whnf_head_pred does not check the given predicate
               before unfolding projections. Moreover, some values are projections applications.
               Example:
                  (@has_zero.zero nat nat.has_zero)
                  (@has_one.one nat nat.has_one)
            */
            return ctx.whnf_head_pred(e, [&](expr const & e) {
                    return !is_constructor_app(ctx, e) && !is_value(ctx, e) && !is_transport_app(e);
                });
        }
    }

    /* Normalize until head is constructor */
    expr whnf_constructor(type_context_old & ctx, expr const & e) {
        return ctx.whnf_head_pred(e, [&](expr const & e) {
                return !is_constructor_app(ctx, e);
            });
    }

    /* Normalize until head is an inductive datatype */
    expr whnf_inductive(type_context_old & ctx, expr const & e) {
        return ctx.whnf_head_pred(e, [&](expr const & e) {
                return !is_inductive_app(e);
            });
    }

    optional<equation> mk_equation(local_context const & lctx, expr const & eqn, unsigned idx) {
        expr it = eqn;
        it = binding_body(it); /* consume fn header */
        if (is_no_equation(it)) return optional<equation>();
        type_context_old ctx = mk_type_context(lctx);
        buffer<expr> locals;
        while (is_lambda(it)) {
            expr type  = instantiate_rev(binding_domain(it), locals);
            expr local = ctx.push_local(binding_name(it), type);
            locals.push_back(local);
            it = binding_body(it);
        }
        lean_assert(is_equation(it));
        equation E;
        bool ignore_if_unused = ignore_equation_if_unused(it);
        m_used_eqns.push_back(ignore_if_unused);
        E.m_vars = to_list(locals);
        E.m_lctx = ctx.lctx();
        E.m_rhs  = instantiate_rev(equation_rhs(it), locals);
        /* The function being defined is not recursive. So, E.m_rhs
           must be closed even if we "consumed" the fn header in
           the beginning of the method. */
        lean_assert(closed(E.m_rhs));
        buffer<expr> lhs_args;
        get_app_args(equation_lhs(it), lhs_args);
        buffer<expr> patterns;
        for (expr & arg : lhs_args) {
            arg = instantiate_rev(arg, locals);
            patterns.push_back(whnf_pattern(ctx, arg));
        }
        E.m_lhs_args = to_list(lhs_args);
        E.m_patterns = to_list(patterns);
        E.m_ref      = eqn;
        E.m_eqn_idx  = idx;
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

    unsigned get_eqns_arity(local_context const & lctx, expr const & eqns) {
        /* Naive way to retrieve the arity of the function being defined */
        lean_assert(is_equations(eqns));
        type_context_old ctx = mk_type_context(lctx);
        unpack_eqns ues(ctx, eqns);
        return ues.get_arity_of(0);
    }

    pair<problem, expr> mk_problem(local_context const & lctx, expr const & e) {
        lean_assert(is_equations(e));
        buffer<expr> eqns;
        to_equations(e, eqns);
        problem P;
        P.m_fn_name    = binding_name(eqns[0]);
        expr fn_type   = binding_domain(eqns[0]);
        expr mvar      = m_mctx.mk_metavar_decl(lctx, fn_type);
        unsigned arity = get_eqns_arity(lctx, e);
        buffer<name> var_names;
        bool use_unused_names = false;
        optional<expr> goal = intron(m_env, get_options(), m_mctx, mvar,
                                     arity, var_names, use_unused_names);
        if (!goal) throw_ill_formed_eqns();
        P.m_goal       = *goal;
        local_context goal_lctx = get_local_context(*goal);
        buffer<expr> vars;
        for (name const & n : var_names)
            vars.push_back(goal_lctx.get_local_decl(n).mk_ref());
        P.m_var_stack  = to_list(vars);
        P.m_example    = P.m_var_stack;
        P.m_equations  = mk_equations(lctx, eqns);
        return mk_pair(P, mvar);
    }

    /* Return true iff the next element in the variable stack is a variable.
       \remark It may not be because of dependent pattern matching. */
    bool is_next_var(problem const & P) {
        lean_assert(P.m_var_stack);
        expr const & x = head(P.m_var_stack);
        return is_local(x);
    }

    template<typename Pred>
    bool all_equations(problem const & P, Pred && p) const {
        for (equation const & eqn : P.m_equations) {
            if (!p(eqn))
                return false;
        }
        return true;
    }

    template<typename Pred>
    bool all_next_pattern(problem const & P, Pred && p) const {
        return all_equations(P, [&](equation const & eqn) {
                lean_assert(eqn.m_patterns);
                return p(head(eqn.m_patterns));
            });
    }

    /* Return true iff the next pattern in all equations is a variable. */
    bool is_variable_transition(problem const & P) const {
        return all_next_pattern(P, is_local);
    }

    /* Return true iff the next pattern in all equations is a constructor. */
    bool is_constructor_transition(problem const & P) {
        return all_equations(P, [&](equation const & eqn) {
                expr const & p = head(eqn.m_patterns);
                type_context_old ctx = mk_type_context(eqn.m_lctx);
                if (is_constructor_app(ctx, p))
                    return true;
                return is_value(ctx, p);
            });
    }

    /* Return true iff the next pattern in all equations is the same invertible function. */
    bool is_transport_transition(problem const & P) {
        if (!P.m_equations) return false;
        optional<name> fn_name;
        return all_next_pattern(P, [&](expr const & p) {
                if (!is_transport_app(p)) return false;
                name const & curr_name = const_name(get_app_fn(p));
                if (fn_name) {
                    return *fn_name == curr_name;
                } else {
                    fn_name = curr_name;
                    return true;
                }
            });
    }

    /* Return true iff the next pattern of every equation is a constructor or variable,
       and there is at least one equation where it is a variable and another where it is a
       constructor. */
    bool is_complete_transition(problem const & P) {
        bool has_variable    = false;
        bool has_constructor = false;
        bool r = all_equations(P, [&](equation const & eqn) {
                expr const & p = head(eqn.m_patterns);
                if (is_local(p)) {
                    has_variable = true; return true;
                }
                type_context_old ctx = mk_type_context(eqn.m_lctx);
                if (is_constructor_app(ctx, p)) {
                    has_constructor = true; return true;
                }
                if (is_value(ctx, p)) {
                    has_constructor = true; return true;
                }
                return false;
            });
        return r && has_variable && has_constructor;
    }

    /* Return true if the next pattern of every equation is a value or variable,
       and there are at least one equation where it is a variable and another where it is a
       value.

       We also perform a value transition if one of the next patterns is a
       string literal.
    */
    bool is_value_transition(problem const & P) {
        bool has_value        = false;
        bool has_variable     = false;
        bool has_finite_value = false;
        bool r = all_equations(P, [&](equation const & eqn) {
                expr const & p = head(eqn.m_patterns);
                if (is_local(p)) {
                    has_variable = true; return true;
                } else {
                    type_context_old ctx = mk_type_context(eqn.m_lctx);
                    if (is_value(ctx, p)) {
                        has_value    = true;
                        if (is_finite_value(ctx, p))
                            has_finite_value = true;
                        return true;
                    } else {
                        return false;
                    }
                }
            });
        if (!r || !has_value)
            return false;
        if (!has_variable && has_finite_value)
            return false;
        type_context_old ctx  = mk_type_context(P);
        /* Check whether other variables on the variable stack depend on the head. */
        expr const & v   = head(P.m_var_stack);
        if (depends_on(ctx.infer(P.m_goal), v)) {
            trace_match(tout() << "variable transition is not used because the target depends on '" << v << "'\n";);
            return false;
        }
        for (expr const & w : tail(P.m_var_stack)) {
            expr w_type = ctx.instantiate_mvars(ctx.infer(w));
            if (depends_on(w_type, v)) {
                trace_match(tout() << "variable transition is not used because type of '" << w << "' depends on '" << v << "'\n";);
                return false;
            }
        }
        return true;
    }

    /** Return true iff the next pattern of some equations is an inaccessible term */
    bool some_inaccessible(problem const & P) const {
        for (equation const & eqn : P.m_equations) {
            lean_assert(eqn.m_patterns);
            expr const & p = head(eqn.m_patterns);
            if (is_inaccessible(p))
                return true;
        }
        return false;
    }

    /** Return true iff the next pattern of all equations is an inaccessible term */
    bool all_inaccessible(problem const & P) const {
        for (equation const & eqn : P.m_equations) {
            lean_assert(eqn.m_patterns);
            expr const & p = head(eqn.m_patterns);
            if (!is_inaccessible(p))
                return false;
        }
        return true;
    }

    /* Return true iff the next pattern in some of the equations is an inaccessible term. */
    bool is_inaccessible_transition(problem const & P) const {
        return some_inaccessible(P);
    }

    /** Replace local `x` in `e` with `renaming.find(x)` */
    expr apply_renaming(expr const & e, name_map<expr> const & renaming) {
        return replace(e, [&](expr const & e, unsigned) {
                if (is_local(e)) {
                    if (auto new_e = renaming.find(mlocal_name(e)))
                        return some_expr(*new_e);
                }
                return none_expr();
            });
    }

    expr get_next_pattern_of(list<equation> const & eqns, unsigned eqn_idx) {
        for (equation const & eqn : eqns) {
            lean_assert(eqn.m_patterns);
            if (eqn.m_eqn_idx == eqn_idx)
                return head(eqn.m_patterns);
        }
        lean_unreachable();
    }

    hsubstitution add_subst(hsubstitution subst, expr const & src, expr const & target) {
        lean_assert(is_local(src));
        if (!subst.contains(mlocal_name(src)))
            subst.insert(mlocal_name(src), target);
        return subst;
    }

    /* Variable and Inaccessible transition are very similar, this method implements both. */
    list<lemma> process_variable_inaccessible(problem const & P, bool is_var_transition) {
        lean_assert(is_variable_transition(P) || is_inaccessible_transition(P));
        lean_assert(is_var_transition == is_variable_transition(P));
        problem new_P;
        new_P.m_fn_name   = P.m_fn_name;
        new_P.m_goal      = P.m_goal;
        new_P.m_var_stack = tail(P.m_var_stack);
        new_P.m_example   = P.m_example;
        buffer<equation> new_eqns;
        for (equation const & eqn : P.m_equations) {
            equation new_eqn   = eqn;
            new_eqn.m_patterns = tail(eqn.m_patterns);
            if (is_var_transition || is_local(head(eqn.m_patterns))) {
                new_eqn.m_subst  = add_subst(eqn.m_subst, head(eqn.m_patterns), head(P.m_var_stack));
            }
            new_eqns.push_back(new_eqn);
        }
        new_P.m_equations = to_list(new_eqns);
        return process(new_P);
    }

    list<lemma> process_variable(problem const & P) {
        trace_match(tout() << "step: variables only\n";);
        return process_variable_inaccessible(P, true);
    }

    list<lemma> process_inaccessible(problem const & P) {
        trace_match(tout() << "step: inaccessible terms only\n";);
        return process_variable_inaccessible(P, false);
    }

    /* Make sure then next pattern of each equation is a constructor application. */
    list<equation> normalize_next_pattern(list<equation> const & eqns) {
        buffer<equation> R;
        for (equation const & eqn : eqns) {
            lean_assert(eqn.m_patterns);
            type_context_old ctx = mk_type_context(eqn.m_lctx);
            /* Remark: reverted bcf44f7020, see issue #1739 */
            /* expr pattern     = whnf_constructor(ctx, head(eqn.m_patterns)); */
            /* We use ctx.relaxed_whnf to make sure we expose the kernel constructor */
            expr pattern     = ctx.relaxed_whnf(head(eqn.m_patterns));
            if (!is_constructor_app(ctx, pattern)) {
                throw_error("equation compiler failed, pattern is not a constructor "
                            "(use 'set_option trace.eqn_compiler.elim_match true' for additional details)");
            }
            equation new_eqn   = eqn;
            new_eqn.m_patterns = cons(pattern, tail(eqn.m_patterns));
            R.push_back(new_eqn);
        }
        return to_list(R);
    }

    /* Append `ilist` and `var_stack`. Due to dependent pattern matching, ilist may contain terms that
       are not local constants. */
    list<expr> update_var_stack(list<expr> const & ilist, list<expr> const & var_stack, hsubstitution const & subst) {
        buffer<expr> new_var_stack;
        for (expr const & e : ilist) {
            new_var_stack.push_back(e);
        }
        for (expr const & v : var_stack) {
            new_var_stack.push_back(apply(v, subst));
        }
        return to_list(new_var_stack);
    }

    /* eqns is the data-structured returned by distribute_constructor_equations.
       This method selects the ones such that eqns[i].first == C.
       It also updates eqns[i].second.m_subst using \c new_subst.
       It also "replaces" the next pattern (a constructor) with its fields.

       The map \c new_subst is produced by the `cases` tactic.
       It is needed because the `cases` tactic may revert and reintroduce hypothesis that
       depend on the hypothesis being destructed. */
    list<equation> get_equations_for(name const & C, unsigned nparams, hsubstitution const & new_subst,
                                     list<equation> const & eqns) {
        buffer<equation> R;
        for (equation const & eqn : eqns) {
            expr pattern = head(eqn.m_patterns);
            buffer<expr> pattern_args;
            expr const & C2 = get_app_args(pattern, pattern_args);
            if (!is_constant(C2, C)) continue;
            equation new_eqn   = eqn;
            new_eqn.m_subst    = apply(eqn.m_subst, new_subst);
            /* Update patterns */
            type_context_old ctx   = mk_type_context(eqn.m_lctx);
            for (unsigned i = nparams; i < pattern_args.size(); i++)
                pattern_args[i] = whnf_pattern(ctx, pattern_args[i]);
            new_eqn.m_patterns = to_list(pattern_args.begin() + nparams, pattern_args.end(), tail(eqn.m_patterns));
            R.push_back(new_eqn);
        }
        return to_list(R);
    }

    optional<list<lemma>> process_constructor_core(problem const & P, bool fail_if_subgoals) {
        trace_match(tout() << "step: constructors only\n";);
        lean_assert(is_constructor_transition(P));
        type_context_old ctx   = mk_type_context(P);
        expr x             = head(P.m_var_stack);
        /* Remark: reverted bcf44f7020, see issue #1739 */
        /* expr x_type        = whnf_inductive(ctx, ctx.infer(x)); */
        expr x_type        = ctx.relaxed_whnf(whnf_inductive(ctx, ctx.infer(x)));
        lean_assert(is_inductive_app(x_type));
        buffer<expr> x_type_args;
        auto x_type_const  = get_app_args(x_type, x_type_args);
        name I_name        = const_name(x_type_const);
        unsigned I_nparams = get_inductive_num_params(I_name);
        lean_assert(x_type_args.size() >= I_nparams);
        intros_list ilist;
        hsubstitution_list slist;
        list<expr> new_goals;
        list<name> new_goal_cnames;
        try {
            /* Remark: reverted bcf44f7020, see issue #1739 */
            /* bool unfold_ginductive = false; */
            bool unfold_ginductive = true;
            list<name> ids;
            std::tie(new_goals, new_goal_cnames) =
                cases(m_env, get_options(), transparency_mode::Semireducible, m_mctx,
                      P.m_goal, x, ids, &ilist, &slist, unfold_ginductive);
            lean_assert(length(new_goals) == length(new_goal_cnames));
            lean_assert(length(new_goals) == length(ilist));
            lean_assert(length(new_goals) == length(slist));
        } catch (exception & ex) {
            throw nested_exception("equation compiler failed (use 'set_option trace.eqn_compiler.elim_match true' "
                                   "for additional details)", ex);
        }
        if (empty(new_goals)) {
            return some(list<lemma>());
        } else if (fail_if_subgoals) {
            return optional<list<lemma>>();
        }
        list<equation> eqns = normalize_next_pattern(P.m_equations);
        buffer<lemma> new_Ls;
        while (new_goals) {
            lean_assert(new_goal_cnames && ilist && slist);
            problem new_P;
            new_P.m_fn_name        = name(P.m_fn_name, head(new_goal_cnames).get_string());
            expr new_goal          = head(new_goals);
            new_P.m_var_stack      = update_var_stack(head(ilist), tail(P.m_var_stack), head(slist));
            new_P.m_goal           = new_goal;
            name const & C         = head(new_goal_cnames);
            new_P.m_example = map(P.m_example, [&] (expr ex) {
                ex = instantiate(abstract_local(ex, head(P.m_var_stack)),
                    mk_app(mk_app(mk_constant(C, const_levels(x_type_const)), I_nparams, x_type_args.begin()), head(ilist)));
                ex = apply(ex, head(slist));
                return ex;
            });
            new_P.m_equations      = get_equations_for(C, I_nparams, head(slist), eqns);
            to_buffer(process(new_P), new_Ls);
            new_goals       = tail(new_goals);
            new_goal_cnames = tail(new_goal_cnames);
            ilist           = tail(ilist);
            slist           = tail(slist);
        }
        return some(to_list(new_Ls));
    }

    list<lemma> process_constructor(problem const & P) {
        bool fail_if_subgoals = false;
        return *process_constructor_core(P, fail_if_subgoals);
    }

    list<lemma> process_value(problem const & P) {
        trace_match(tout() << "step: if-then-else\n";);
        bool is_last       = !tail(P.m_var_stack);
        expr x             = head(P.m_var_stack);
        local_context lctx = get_local_context(P.m_goal);
        type_context_old ctx   = mk_type_context(P);
        expr goal_type     = ctx.infer(P.m_goal);
        expr else_goal     = ctx.mk_metavar_decl(lctx, goal_type);
        buffer<expr> values;
        buffer<expr> value_goals;
        buffer<expr> eqs;
        for (equation const & eqn : P.m_equations) {
            expr const & p = head(eqn.m_patterns);
            if (is_last && is_local(p))
                break;
            if (!is_local(p) &&
                std::find(values.begin(), values.end(), p) == values.end()) {
                values.push_back(p);
                value_goals.push_back(ctx.mk_metavar_decl(lctx, goal_type));
                expr const & eq = mk_eq(ctx, x, p);
                eqs.push_back(eq);
            }
        }
        expr goal_val = else_goal;
        unsigned i    = value_goals.size();
        while (i > 0) {
            --i;
            goal_val  = mk_ite(ctx, eqs[i], value_goals[i], goal_val);
        }
        m_mctx = ctx.mctx();
        m_mctx.assign(P.m_goal, goal_val);
        buffer<lemma> new_Ls;
        for (unsigned i = 0; i < values.size(); i++) {
            /* Process equations for values[i] */
            problem new_P;
            expr val          = values[i];
            new_P.m_fn_name   = name(P.m_fn_name, "_ite_val");
            new_P.m_goal      = value_goals[i];
            new_P.m_var_stack = tail(P.m_var_stack);
            new_P.m_example   = cons(val, tail(P.m_example));
            buffer<equation> new_eqns;
            for (equation const & eqn : P.m_equations) {
                expr const & p = head(eqn.m_patterns);
                if (p == val) {
                    equation new_eqn    = eqn;
                    new_eqn.m_patterns  = tail(new_eqn.m_patterns);
                    new_eqns.push_back(new_eqn);
                    if (is_last) break;
                } else if (is_local(p)) {
                    /* Replace variable `p` with `val` in this equation */
                    type_context_old ctx   = mk_type_context(eqn.m_lctx);
                    buffer<expr> from;
                    buffer<expr> to;
                    buffer<expr> new_vars;
                    for (expr const & curr : eqn.m_vars) {
                        if (curr == p) {
                            from.push_back(p);
                            to.push_back(val);
                        } else {
                            expr curr_type     = ctx.infer(curr);
                            expr new_curr_type = replace_locals(curr_type, from, to);
                            if (curr_type == new_curr_type) {
                                new_vars.push_back(curr);
                            } else {
                                expr new_curr = ctx.push_local(mlocal_pp_name(curr), new_curr_type);
                                from.push_back(curr);
                                to.push_back(new_curr);
                                new_vars.push_back(new_curr);
                            }
                        }
                    }
                    equation new_eqn   = eqn;
                    new_eqn.m_vars     = to_list(new_vars);
                    new_eqn.m_lctx     = ctx.lctx();
                    new_eqn.m_lhs_args = map(eqn.m_lhs_args, [&](expr const & arg) {
                            return replace_locals(arg, from, to); });
                    new_eqn.m_rhs      = replace_locals(eqn.m_rhs, from, to);
                    new_eqn.m_patterns = map(tail(eqn.m_patterns), [&](expr const & p) {
                            return replace_locals(p, from, to); });
                    new_eqns.push_back(new_eqn);
                    if (is_last) break;
                }
            }
            new_P.m_equations = to_list(new_eqns);
            to_buffer(process(new_P), new_Ls);
        }
        {
            /* Else-case */
            problem new_P;
            new_P.m_fn_name   = name(P.m_fn_name, "_ite_else");
            new_P.m_goal      = else_goal;
            new_P.m_var_stack = tail(P.m_var_stack);
            new_P.m_example   = P.m_example;
            buffer<equation> new_eqns;
            for (equation const & eqn : P.m_equations) {
                expr const & p = head(eqn.m_patterns);
                if (is_local(p)) {
                    equation new_eqn = eqn;
                    new_eqn.m_patterns = tail(new_eqn.m_patterns);
                    new_eqn.m_subst    = add_subst(eqn.m_subst, p, x);
                    type_context_old ctx   = mk_type_context(eqn.m_lctx);
                    new_eqn.m_hs       = eqn.m_hs;
                    unsigned idx       = length(eqn.m_hs) + 1;
                    for (unsigned i = 0; i < values.size(); i++) {
                        expr eq        = mk_eq(ctx, p, values[i]);
                        expr ne        = mk_not(ctx, eq);
                        expr H         = ctx.push_local(name("_h").append_after(idx), ne);
                        idx++;
                        new_eqn.m_hs   = cons(H, new_eqn.m_hs);
                    }
                    new_eqn.m_lctx     = ctx.lctx();
                    new_eqns.push_back(new_eqn);
                    if (is_last) break;
                }
            }
            new_P.m_equations = to_list(new_eqns);
            to_buffer(process(new_P), new_Ls);
        }
        return to_list(new_Ls);
    }

    list<lemma> process_complete(problem const & P) {
        lean_assert(is_complete_transition(P));
        trace_match(tout() << "step: variables and constructors\n";);
        /* The next pattern of every equation is a constructor or variable.
           We split the equations where the next pattern is a variable into cases.
           That is, we are reducing this case to the compile_constructor case. */
        buffer<equation> new_eqns;
        for (equation const & eqn : P.m_equations) {
            expr const & pattern = head(eqn.m_patterns);
            if (is_local(pattern)) {
                type_context_old ctx  = mk_type_context(eqn.m_lctx);
                for_each_compatible_constructor(ctx, pattern,
                    [&](expr const & c, buffer<expr> const & new_c_vars) {
                    expr var = pattern;
                    /* We are replacing `var` with `c` */
                    buffer<expr> vars; to_buffer(eqn.m_vars, vars);
                    buffer<expr> new_vars;
                    buffer<expr> from;
                    buffer<expr> to;
                    update_telescope(ctx, vars, var, c, new_c_vars, new_vars, from, to);
                    equation new_eqn   = eqn;
                    new_eqn.m_lctx     = ctx.lctx();
                    new_eqn.m_vars     = to_list(new_vars);
                    new_eqn.m_lhs_args = map(eqn.m_lhs_args, [&](expr const & arg) {
                            return replace_locals(arg, from, to); });
                    new_eqn.m_rhs      = replace_locals(eqn.m_rhs, from, to);
                    new_eqn.m_patterns =
                    cons(c, map(tail(eqn.m_patterns), [&](expr const & p) {
                                return replace_locals(p, from, to); }));
                    new_eqns.push_back(new_eqn);
                });
            } else {
                new_eqns.push_back(eqn);
            }
        }
        problem new_P = P;
        new_P.m_equations = to_list(new_eqns);
        return process(new_P);
    }

    list<lemma> process_no_equation(problem const & P) {
        if (!is_next_var(P)) {
            return process_variable(P);
        } else {
            type_context_old ctx = mk_type_context(P);
            expr x           = head(P.m_var_stack);
            expr arg_type    = ctx.infer(x);
            if (is_below_type(arg_type)) {
                return process_variable(P);
            } else {
                expr I = whnf_inductive(ctx, arg_type);
                if (is_inductive_app(I)) {
                    metavar_context saved_mctx = m_mctx;
                    bool fail_if_subgoals      = is_recursive_datatype(m_env, const_name(get_app_fn(I)));
                    optional<list<lemma>> r;
                    try {
                        r = process_constructor_core(P, fail_if_subgoals);
                    } catch (exception &) {}
                    if (r) {
                        return list<lemma>();
                    } else {
                        /* Process_constructor_core produced subgoals for recursive datatype,
                           this may produce non-termination. So, if fail and handle it as a variable case. */
                        m_mctx = saved_mctx;
                        return process_variable(P);
                    }
                } else {
                    return process_variable(P);
                }
            }
        }
    }

    list<lemma> process_non_variable(problem const & P) {
        expr p = head(P.m_var_stack);
        lean_assert(!is_local(p));
        type_context_old ctx = mk_type_context(P);
        if (all_inaccessible(P)) {
            trace_match(tout() << "step: skip inaccessible patterns\n";);
            problem new_P;
            new_P.m_fn_name   = P.m_fn_name;
            new_P.m_goal      = P.m_goal;
            new_P.m_example   = P.m_example;
            new_P.m_var_stack = tail(P.m_var_stack);
            buffer<equation> new_eqns;
            for (equation const & eqn : P.m_equations) {
                equation new_eqn   = eqn;
                new_eqn.m_patterns = tail(eqn.m_patterns);
                new_eqns.push_back(new_eqn);
            }
            new_P.m_equations = to_list(new_eqns);
            return process(new_P);
        } else {
            trace_match(tout() << "step: filter equations using constructor\n";);
            p      = whnf_constructor(ctx, p);
            if (!is_constructor_app(ctx, p)) {
                throw_error("dependent pattern matching result is not a constructor application "
                            "(use 'set_option trace.eqn_compiler.elim_match true' "
                            "for additional details)");
            }
            expr p_type         = whnf_inductive(ctx, ctx.infer(p));
            lean_assert(is_inductive_app(p_type));
            name I_name         = const_name(get_app_fn(p_type));
            unsigned I_nparams  = get_inductive_num_params(I_name);
            buffer<expr> C_args;
            expr const & C      = get_app_args(p, C_args);
            list<equation> eqns = normalize_next_pattern(P.m_equations);
            problem new_P;
            new_P.m_fn_name     = P.m_fn_name;
            new_P.m_goal        = P.m_goal;
            new_P.m_example     = P.m_example;
            buffer<expr> new_var_stack;
            for (unsigned i = I_nparams; i < C_args.size(); i++) {
                new_var_stack.push_back(whnf_constructor(ctx, C_args[i]));
            }
            to_buffer(tail(P.m_var_stack), new_var_stack);
            new_P.m_var_stack   = to_list(new_var_stack);
            new_P.m_equations   = get_equations_for(const_name(C), I_nparams, hsubstitution(), eqns);
            return process(new_P);
        }
    }

    /* Create (f ... x) with the given arity, where the other arguments are inferred using
       type inference */
    expr mk_app_with_arity(type_context_old & ctx, name const & f, unsigned arity, expr const & x) {
        buffer<bool> mask;
        mask.resize(arity - 1, false);
        mask.push_back(true);
        try {
            return mk_app(ctx, f, mask.size(), mask.data(), &x);
        } catch (app_builder_exception &) {
            throw_error(sstream() << "equation compiler failed, when trying to build "
                        << "'" << f << "' application (use 'set_option trace.eqn_compiler.elim_match true' "
                        << "for additional details)");
        }
    }

    /*
      This step is applied to problems of the form

      goal:       ... (x : A) ... |- C x
      var_stack:  [x, ...]
      equations:
             (f y_1) ... := rhs_1
             (f y_2) ... := rhs_2
             ...
             (f y_n) ... := rhs_n

      where f (B -> A) is not a constructor, and there is a function g : A -> B s.t.
         g_f_eq :  forall y, g (f y) = y
         f_g_eq :  forall x, f (g x) = x

      Steps:

      1) Revert x and obtain goal

      M_1  ...  |- forall (x : A), C' x

      2) Create new goal

      M_2  ...  |- forall (y : B), C' (f y)

      Solution for M_1 is

           fun x : A, @@eq.rec (fun x, C' x) (M_2 (g x)) (f_g_eq x)

      We need the eq.rec because (M_2 (g x)) has type (C' (f (g x)))

      3) Create new problem by reintroducing all variables inverted in
      step 1, replacing x with y in the var stack, and using the new set of equations

             y_1 ... := rhs_1
             y_2 ... := rhs_2
             ...
             y_n ... := rhs_n

      Remark: the lemma g_f_eq is used when we are trying to prove the equation lemmas.
    */
    list<lemma> process_transport(problem const & P) {
        trace_match(tout() << "step: transport function\n";);
        expr x                = head(P.m_var_stack);
        expr p                = head(head(P.m_equations).m_patterns);
        lean_assert(is_transport_app(p));
        expr f                = get_app_fn(p);
        name f_name           = const_name(f);
        inverse_info info     = *has_inverse(m_env, f_name);
        unsigned f_arity      = info.m_arity;
        name g_name           = info.m_inv;
        unsigned g_arity      = info.m_inv_arity;
        inverse_info info_inv = *has_inverse(m_env, g_name);
        name f_g_eq_name      = info_inv.m_lemma;

        /* Step 1 */
        buffer<expr> to_revert;
        to_revert.push_back(x);
        bool preserve_to_revert_order = true; /* it is a don't care since to_revert has size 1 */
        expr M_1           = revert(m_env, get_options(), m_mctx, P.m_goal, to_revert, preserve_to_revert_order);

        /* Step 2 */
        type_context_old ctx1  = mk_type_context(M_1);
        expr M_1_type      = ctx1.relaxed_whnf(ctx1.infer(M_1));
        lean_assert(is_pi(M_1_type));
        expr x1            = ctx1.push_local(binding_name(M_1_type), binding_domain(M_1_type));
        expr g_x1          = mk_app_with_arity(ctx1, g_name, g_arity, x1);
        expr B             = ctx1.infer(g_x1);
        expr y1            = ctx1.push_local("_y", B);
        expr f_y1          = mk_app_with_arity(ctx1, f_name, f_arity, y1);
        expr C_x1          = instantiate(binding_body(M_1_type), x1);
        expr C_f_y1        = replace_local(C_x1, x1, f_y1);
        expr M_2_type      = ctx1.mk_pi(y1, C_f_y1);
        expr M_2           = ctx1.mk_metavar_decl(get_local_context(M_1), M_2_type);
        expr eqrec;
        try {
            expr eqrec_motive  = ctx1.mk_lambda(x1, C_x1);
            /* When proving equation lemmas, we need to be able to identify the value M2 was assigned to.
               If we use just (M2 (g x1)) as eqrec_minor, there is a risk beta-reduction is performed
               when instatiating the metavariable M2. We avoid the beta-reduction by wrapping
               M2 with the identity function. */
            expr id_M2         = mk_app(ctx1, get_id_name(), M_2);
            expr eqrec_minor   = mk_app(id_M2, g_x1);
            expr eqrec_major   = mk_app(ctx1, f_g_eq_name, x1);
            eqrec              = mk_eq_rec(ctx1, eqrec_motive, eqrec_minor, eqrec_major);
        } catch (app_builder_exception &) {
            throw_error("equation compiler failed, when trying to build "
                        "'eq.rec'-application for transport step (use 'set_option trace.eqn_compiler.elim_match true' "
                        "for additional details)");
        }
        expr M_1_val       = ctx1.mk_lambda(x1, eqrec);
        /* M_1_val is (fun x1 : A, @@eq.rec (fun x1, C x1) ((id M_2) (g x1)) (f_g_eq x1)) */
        m_mctx             = ctx1.mctx();
        m_mctx.assign(M_1, M_1_val);

        /* Step 3 */
        buffer<name> new_H_names;
        bool use_unused_names = false;
        optional<expr> M_3 = intron(m_env, get_options(), m_mctx, M_2, to_revert.size(), new_H_names, use_unused_names);
        if (!M_3) {
            throw_error("equation compiler failed, when reintroducing reverted variables "
                        "(use 'set_option trace.eqn_compiler.elim_match true' "
                        "for additional details)");
        }
        local_context lctx3 = get_local_context(*M_3);
        buffer<expr> new_Hs;
        for (name const & H_name : new_H_names) {
            new_Hs.push_back(lctx3.get_local(H_name));
        }
        lean_assert(to_revert.size() == new_Hs.size());
        problem new_P;
        new_P.m_fn_name   = name(P.m_fn_name, "_transport");
        new_P.m_goal      = *M_3;
        new_P.m_var_stack = map(P.m_var_stack,
                                [&](expr const & x) { return replace_locals(x, to_revert, new_Hs); });
        new_P.m_example   = map(P.m_example, [&] (expr ex) {
            auto f_x = instantiate(abstract_local(f_y1, y1), x);
            ex = instantiate(abstract_local(ex, x), f_x);
            ex = replace_locals(ex, to_revert, new_Hs);
            return ex;
        });
        buffer<equation> new_eqns;
        for (equation const & eqn : P.m_equations) {
            equation new_eqn   = eqn;
            expr const & p     = head(eqn.m_patterns);
            expr new_p         = app_arg(p);
            new_eqn.m_patterns = cons(new_p, tail(eqn.m_patterns));
            new_eqns.push_back(new_eqn);
        }
        new_P.m_equations  = to_list(new_eqns);
        return process(new_P);
    }

    list<lemma> process_leaf(problem const & P) {
        if (!P.m_equations) {
            m_unsolved.push_back(P);
            m_mctx.assign(P.m_goal, mk_sorry(m_mctx.get_metavar_decl(P.m_goal).get_type(), true));
            return list<lemma>();
        }
        equation const & eqn       = head(P.m_equations);
        m_used_eqns[eqn.m_eqn_idx] = true;
        expr rhs                   = apply(eqn.m_rhs, eqn.m_subst);
        if (m_env.find(get_id_rhs_name())) {
            /* We wrap the rhs with `id_rhs` to solve a performance problem related to whnf_ite when proving
               the equational lemmas.

               We use `id_rhs` as a marker at whnf_ite. The goal is to stop whnf computation as soon as we find
               an `id_rhs` application at whnf_ite.

               Remark: `id_rhs` is defined using `abbrev` hint. So, the is_def_eq procedure in the kernel
               is not affected by it. That is, a problem
                       t =?= id_rhs s
               is reduced to
                       t =?= s


               Remark: we also use `id_rhs` to implement "smart reduction" at type_context_old.
            */
            type_context_old ctx = mk_type_context(P);
            rhs              = mk_id_rhs(ctx, rhs);
        }
        m_mctx.assign(P.m_goal, rhs);
        if (m_aux_lemmas) {
            lemma L;
            L.m_lctx     = eqn.m_lctx;
            L.m_vars     = eqn.m_vars;
            L.m_hs       = eqn.m_hs;
            L.m_lhs_args = erase_inaccessible_annotations(eqn.m_lhs_args);
            L.m_rhs      = eqn.m_rhs;
            L.m_eqn_idx  = eqn.m_eqn_idx;
            return to_list(L);
        } else {
            return list<lemma>();
        }
    }

    list<lemma> process(problem const & P) {
        flet<unsigned> inc_depth(m_depth, m_depth+1);
        trace_match(tout() << "depth [" << m_depth << "]\n" << pp_problem(P) << "\n";);
        lean_assert(check_problem(P));
        m_num_steps++;
        try {
            if (m_num_steps > m_max_steps) {
                throw_error(sstream() << "equation compiler failed, maximum number of steps (" << m_max_steps << ") exceeded"
                            << " (possible solution: use 'set_option eqn_compiler.max_steps <new-threshold>')"
                            << " (use 'set_option trace.eqn_compiler.elim_match true' for additional details)");
            }
            if (P.m_var_stack) {
                if (!P.m_equations) {
                    return process_no_equation(P);
                } else if (!is_next_var(P)) {
                    return process_non_variable(P);
                } else if (is_variable_transition(P)) {
                    return process_variable(P);
                } else if (is_value_transition(P)) {
                    return process_value(P);
                } else if (is_complete_transition(P)) {
                    return process_complete(P);
                } else if (is_constructor_transition(P)) {
                    return process_constructor(P);
                } else if (is_transport_transition(P)) {
                    return process_transport(P);
                } else if (is_inaccessible_transition(P)) {
                    return process_inaccessible(P);
                } else {
                    trace_match(tout() << "compilation failed at\n" << pp_problem(P) << "\n";);
                    throw_error("equation compiler failed (use 'set_option trace.eqn_compiler.elim_match true' "
                                "for additional details)");
                }
            } else {
                return process_leaf(P);
            }
        } catch (exception & ex) {
            if (!m_elab.try_report(ex, some_expr(m_ref))) throw;
            m_error_during_process = true;
            m_mctx.assign(P.m_goal, mk_sorry(m_mctx.get_metavar_decl(P.m_goal).get_type(), true));
        }
        return list<lemma>();
    }

    expr finalize_lemma(expr const & fn, lemma const & L) {
        buffer<expr> args;
        to_buffer(L.m_lhs_args, args);
        type_context_old ctx = mk_type_context(L.m_lctx);
        expr lhs = mk_app(fn, args);
        expr eq  = mk_eq(ctx, lhs, L.m_rhs);
        buffer<expr> locals;
        to_buffer(L.m_vars, locals);
        to_buffer(L.m_hs, locals);
        return ctx.mk_pi(locals, eq);
    }

    list<expr> finalize_lemmas(expr const & fn, list<lemma> const & Ls) {
        return map2<expr>(Ls, [&](lemma const & L) { return finalize_lemma(fn, L); });
    }

    void check_no_unused_eqns(expr const & eqns) {
        for (unsigned i = 0; i < m_used_eqns.size(); i++) {
            if (!m_used_eqns[i]) {
                buffer<expr> eqns_buffer;
                to_equations(eqns, eqns_buffer);
                /* Check if there is an equation occurring before #i s.t. the lhs is of the form
                     (f x)
                   where x is a variable */
                unsigned j = 0;
                for (; j < i; j++) {
                    expr eqn_j = eqns_buffer[j];
                    while (is_lambda(eqn_j))
                        eqn_j = binding_body(eqn_j);
                    if (is_equation(eqn_j)) {
                        buffer<expr> lhs_args;
                        get_app_args(equation_lhs(eqn_j), lhs_args);
                        if (lhs_args.size() == 1 && is_var(lhs_args[0]))
                            break; // found it
                    }
                }
                expr ref = eqns_buffer[i];
                while (is_lambda(ref)) ref = binding_body(ref);
                if (j != i) {
                    m_elab.report_or_throw(elaborator_exception(ref,
                                  sstream() << "equation compiler error, equation #" << (i+1)
                                            << " has not been used in the compilation, note that the left-hand-side of equation #" << (j+1)
                                            << " is a variable"));
                } else {
                    m_elab.report_or_throw(elaborator_exception(ref,
                                  sstream() << "equation compiler error, equation #" << (i+1)
                                            << " has not been used in the compilation (possible solution: delete equation)"));
                }
            }
        }
    }

    list<list<expr>> get_counter_examples() {
        buffer<list<expr>> counter_examples;

        auto underscore = mk_expr_placeholder();
        for (auto & P : m_unsolved) {
            counter_examples.push_back(map(P.m_example, [&] (expr const & e) {
                return replace(e, [&] (expr const & e, unsigned) {
                    if (!has_local(e)) return some_expr(e);
                    if (is_local(e)) return some_expr(underscore);
                    return none_expr();
                });
            }));
        }

        return to_list(counter_examples);
    }

    elim_match_result operator()(local_context const & lctx, expr const & eqns) {
        lean_assert(equations_num_fns(eqns) == 1);
        DEBUG_CODE({
                type_context_old ctx = mk_type_context(lctx);
                lean_assert(!is_recursive_eqns(ctx, eqns));
            });
        m_aux_lemmas             = get_equations_header(eqns).m_aux_lemmas;
        m_ref                    = eqns;
        problem P; expr fn;
        std::tie(P, fn)          = mk_problem(lctx, eqns);
        lean_assert(check_problem(P));
        list<lemma> pre_Ls       = process(P);
        auto counter_examples    = get_counter_examples();
        if (!counter_examples && !m_error_during_process)
            check_no_unused_eqns(eqns);
        /* The method `process` may create many common subexpressions because of wildcards occurring in patterns.
           We reduce this redundancy and improve the performance with the function max_sharing.
           The performace improvement can be observed in the following example:
           ```
           universes u

           inductive node (α : Type u)
           | leaf : node
           | red_node : node → α → node → node
           | black_node : node → α → node → node

           namespace node
           variable {α : Type u}

           def balance : node α → α → node α → node α
           | (red_node (red_node a x b) y c) k d := red_node (black_node a x b) y (black_node c k d)
           | (red_node a x (red_node b y c)) k d := red_node (black_node a x b) y (black_node c k d)
           | l k r                               := black_node l k r

           end node
           ```
           It produces 121 equations.
           At commit 47994fe14ec7982d5b727c4f8a4f29ae9abce95c, `balance` takes 781 ms to be elaborated
           on Leo's office desktop. Most of the time is spent proving equation lemmas.
           The runtime is reduced to 479 ms after we added max_sharing.
        */
        fn                       = max_sharing(m_mctx.instantiate_mvars(fn));
        trace_match_debug(tout() << "code:\n" << fn << "\n";);
        list<expr> Ls            = finalize_lemmas(fn, pre_Ls);
        return { fn, Ls, counter_examples };
    }
};

elim_match_result elim_match(environment & env, elaborator & elab, metavar_context & mctx,
                             local_context const & lctx, expr const & eqns) {
    elim_match_fn elim(env, elab, mctx);
    auto r = elim(lctx, eqns);
    env = elim.m_env;
    return r;
}

static expr get_fn_type_from_eqns(expr const & eqns) {
    /* TODO(Leo): implement more efficient version if needed */
    buffer<expr> eqn_buffer;
    to_equations(eqns, eqn_buffer);
    return binding_domain(eqn_buffer[0]);
}

eqn_compiler_result mk_nonrec(environment & env, elaborator & elab, metavar_context & mctx,
                              local_context const & lctx, expr const & eqns) {
    equations_header header = get_equations_header(eqns);
    auto R = elim_match(env, elab, mctx, lctx, eqns);
    if (header.m_is_meta || header.m_is_lemma) {
        /* Do not generate auxiliary equation or equational lemmas */
        auto fn = mk_constant(head(header.m_fn_names));
        auto counter_examples = map2<expr>(R.m_counter_examples, [&] (list<expr> const & e) { return mk_app(fn, e); });
        return { {R.m_fn}, counter_examples };
    }
    type_context_old ctx1(env, mctx, lctx, elab.get_cache(), transparency_mode::Semireducible);
    /*
       We should use the type specified at eqns instead of m_ctx.infer(R.m_fn).
       These two types must be definitionally equal, but the shape of
       m_ctx.infer(R.m_fn) may confuse automaton. For example,
       it might be of the form (Pi (_a : nat), (fun x, nat) _a) which is
       definitionally equal to (nat -> nat), but may confuse simplifier and
       congruence closure modules make them "believe" that this is
       a dependent function.
    */
    expr fn_type        = get_fn_type_from_eqns(eqns);
    name fn_name        = head(header.m_fn_names);
    name fn_actual_name = head(header.m_fn_actual_names);
    expr fn;
    std::tie(env, fn) = mk_aux_definition(env, elab.get_options(), mctx, lctx, header,
                                          fn_name, fn_actual_name, fn_type, R.m_fn);
    unsigned eqn_idx     = 1;
    type_context_old ctx2(env, mctx, lctx, elab.get_cache(), transparency_mode::Semireducible);
    for (expr type : R.m_lemmas) {
        type_context_old::tmp_locals locals(ctx2);
        type = ctx2.relaxed_whnf(type);
        while (is_pi(type)) {
            expr local = locals.push_local_from_binding(type);
            type = instantiate(binding_body(type), local);
        }
        lean_assert(is_eq(type));
        expr lhs = app_arg(app_fn(type));
        expr rhs = app_arg(type);
        buffer<expr> lhs_args;
        get_app_args(lhs, lhs_args);
        expr new_lhs = mk_app(fn, lhs_args);
        env = mk_equation_lemma(env, elab.get_options(), mctx, ctx2.lctx(), fn_name, fn_actual_name,
                                eqn_idx, header.m_is_private, locals.as_buffer(), new_lhs, rhs);
        eqn_idx++;
    }
    auto counter_examples = map2<expr>(R.m_counter_examples, [&] (list<expr> const & e) { return mk_app(fn, e); });
    return { {fn}, counter_examples };
}

void initialize_elim_match() {
    register_trace_class({"eqn_compiler", "elim_match"});
    register_trace_class({"debug", "eqn_compiler", "elim_match"});

    g_eqn_compiler_ite       = new name{"eqn_compiler", "ite"};
    g_eqn_compiler_max_steps = new name{"eqn_compiler", "max_steps"};
    register_bool_option(*g_eqn_compiler_ite, LEAN_DEFAULT_EQN_COMPILER_ITE,
                         "(equation compiler) use if-then-else terms when pattern matching on simple values "
                         "(e.g., strings and characters)");
    register_unsigned_option(*g_eqn_compiler_max_steps, LEAN_DEFAULT_EQN_COMPILER_MAX_STEPS,
                             "(equation compiler) maximum number of pattern matching compilation steps");
}
void finalize_elim_match() {
    delete g_eqn_compiler_ite;
    delete g_eqn_compiler_max_steps;
}
}
