/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <vector>
#include "util/list.h"
#include "kernel/metavar.h"
#include "kernel/type_checker.h"
#include "library/expr_lt.h"
#include "library/unifier.h"
#include "library/local_context.h"
#include "library/tactic/tactic.h"
#include "library/tactic/elaborate.h"
#include "frontends/lean/elaborator_context.h"
#include "frontends/lean/coercion_elaborator.h"
#include "frontends/lean/util.h"
#include "frontends/lean/calc_proof_elaborator.h"
#include "frontends/lean/obtain_expr.h"

namespace lean {
/** \brief Mapping from metavariable names to metavariable applications (?M ...) */
typedef name_map<expr> mvar2meta;

/** \brief Helper class for implementing the \c elaborate functions. */
class elaborator : public coercion_info_manager {
    typedef name_map<expr> local_tactic_hints;
    typedef rb_map<expr, pair<expr, constraint_seq>, expr_quick_cmp> cache;
    typedef std::vector<pair<expr, expr>> to_check_sorts;
    elaborator_context & m_ctx;
    name_generator       m_ngen;
    type_checker_ptr     m_tc;
    type_checker_ptr     m_coercion_from_tc;
    type_checker_ptr     m_coercion_to_tc;
    // mapping from metavariable ?m to the (?m l_1 ... l_n) where [l_1 ... l_n] are the local constants
    // representing the context where ?m was created.
    local_context        m_context; // current local context: a list of local constants
    local_context        m_full_context; // superset of m_context, it also contains non-contextual locals.
    mvar2meta            m_mvar2meta;
    cache                m_cache;
    // The following vector contains sorts that we should check
    // whether the computed universe is too specific or not.
    to_check_sorts       m_to_check_sorts;

    // mapping from metavariable name ?m to tactic expression that should be used to solve it.
    // this mapping is populated by the 'by tactic-expr' expression.
    local_tactic_hints   m_local_tactic_hints;
    name_set             m_used_local_tactic_hints;
    // set of metavariables that we already reported unsolved/unassigned
    name_set             m_displayed_errors;
    // if m_no_info is true, we do not collect information when true,
    // we set is to true whenever we find no_info annotation.
    bool                 m_no_info;
    // if m_in_equation_lhs is true, we are processing the left-hand-side of an equation
    // and inaccessible expressions are allowed
    bool                 m_in_equation_lhs;
    // if m_equation_lhs is not none, we are processing the right-hand-side of an equation
    // and decreasing expressions are allowed
    optional<expr>       m_equation_lhs;
    // if m_equation_R is not none when elaborator is processing recursive equation using the well-founded relation R.
    optional<expr>       m_equation_R;
    bool                 m_use_tactic_hints;
    info_manager         m_pre_info_data;
    bool                 m_has_sorry;
    unifier_config       m_unifier_config;
    // If m_nice_mvar_names is true, we append (when possible) a more informative name for a metavariable.
    // That is, whenever a metavariables comes from a binding, we add the binding name as a suffix
    bool                 m_nice_mvar_names;

    optional<expr>       m_to_show_hole; // type information for "show hole" command line
    expr                 m_to_show_hole_ref; // provide position information
    struct choice_expr_elaborator;

    environment const & env() const { return m_ctx.m_env; }
    io_state const & ios() const { return m_ctx.m_ios; }
    local_decls<level> const & lls() const { return m_ctx.m_lls; }
    bool use_local_instances() const { return m_ctx.m_use_local_instances; }
    info_manager * infom() const { return m_ctx.m_info_manager; }
    pos_info_provider const * pip() const { return m_ctx.m_pos_provider; }
    bool check_unassigned() const { return m_ctx.m_check_unassigned; }

    expr mk_local(name const & n, expr const & t, binder_info const & bi);

    pair<expr, constraint_seq> infer_type(expr const & e) { return m_tc->infer(e); }
    pair<expr, constraint_seq> whnf(expr const & e) { return m_tc->whnf(e); }
    expr infer_type(expr const & e, constraint_seq & s) { return m_tc->infer(e, s); }
    expr whnf(expr const & e, constraint_seq & s) { return m_tc->whnf(e, s); }
    bool is_def_eq(expr const & e1, expr const & e2, justification const & j, constraint_seq & cs) {
        return m_tc->is_def_eq(e1, e2, j, cs);
    }
    expr mk_app(expr const & f, expr const & a, tag g) { return ::lean::mk_app(f, a, g); }

    void register_meta(expr const & meta);

    optional<expr> mvar_to_meta(expr const & mvar);
    void save_type_data(expr const & e, expr const & r);
    void save_binder_type(expr const & e, expr const & r);
    void save_extra_type_data(expr const & e, expr const & r);
    void save_proof_state_info(proof_state const & ps, expr const & e);
    void save_identifier_info(expr const & f);
    void save_synth_data(expr const & e, expr const & r);
    void save_placeholder_info(expr const & e, expr const & r);
    virtual void save_coercion_info(expr const & e, expr const & c);
    virtual void erase_coercion_info(expr const & e);
    void instantiate_info(substitution s);
    /** \brief If info manager is being used, then create a metavariable suffix based on binding_name(b) */
    optional<name> mk_mvar_suffix(expr const & b);
    expr mk_placeholder_meta(optional<name> const & suffix, optional<expr> const & type,
                             tag g, bool is_strict, bool inst_implicit, constraint_seq & cs);
    expr mk_placeholder_meta(optional<expr> const & type, tag g, bool is_strict, bool inst_implicit, constraint_seq & cs) {
        return mk_placeholder_meta(optional<name>(), type, g, is_strict, inst_implicit, cs);
    }

    expr visit_expecting_type(expr const & e, constraint_seq & cs);
    expr visit_expecting_type_of(expr const & e, expr const & t, constraint_seq & cs);
    expr visit_choice(expr const & e, optional<expr> const & t, constraint_seq & cs);
    expr visit_by(expr const & e, optional<expr> const & t, constraint_seq & cs);
    expr visit_by_plus(expr const & e, optional<expr> const & t, constraint_seq & cs);
    expr visit_calc_proof(expr const & e, optional<expr> const & t, constraint_seq & cs);
    expr add_implict_args(expr e, constraint_seq & cs);
    pair<expr, expr> ensure_fun(expr f, constraint_seq & cs);
    bool has_coercions_from(expr const & a_type, bool & lifted_coe);
    bool has_coercions_to(expr d_type);
    expr apply_coercion(expr const & a, expr a_type, expr d_type);
    pair<expr, constraint_seq> mk_delayed_coercion(expr const & a, expr const & a_type, expr const & expected_type,
                                                   justification const & j);
    pair<expr, constraint_seq> ensure_has_type_core(expr const & a, expr const & a_type, expr const & expected_type,
                                                    bool use_expensive_coercions, justification const & j);
    pair<expr, constraint_seq> ensure_has_type(expr const & a, expr const & a_type, expr const & expected_type,
                                               justification const & j) {
        return ensure_has_type_core(a, a_type, expected_type, true, j);
    }
    bool is_choice_app(expr const & e);
    expr visit_choice_app(expr const & e, constraint_seq & cs);
    expr visit_app(expr const & e, constraint_seq & cs);
    expr visit_placeholder(expr const & e, constraint_seq & cs);
    level replace_univ_placeholder(level const & l);
    expr visit_sort(expr const & e);
    expr visit_macro(expr const & e, constraint_seq & cs);
    expr visit_constant(expr const & e);
    expr ensure_type(expr const & e, constraint_seq & cs);
    expr instantiate_rev_locals(expr const & a, unsigned n, expr const * subst);
    expr visit_binding(expr e, expr_kind k, constraint_seq & cs);
    expr visit_pi(expr const & e, constraint_seq & cs);
    expr visit_lambda(expr const & e, constraint_seq & cs);
    expr visit_typed_expr(expr const & e, constraint_seq & cs);
    expr visit_let_value(expr const & e, constraint_seq & cs);
    bool is_sorry(expr const & e) const;
    expr visit_sorry(expr const & e);
    expr visit_core(expr const & e, constraint_seq & cs);
    pair<expr, constraint_seq> visit(expr const & e);
    expr visit(expr const & e, constraint_seq & cs);
    unify_result_seq solve(constraint_seq const & cs);
    void display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg, expr const & pos);
    void display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg);
    void display_unsolved_subgoals(expr const & mvar, proof_state const & ps, expr const & pos);
    void display_unsolved_subgoals(expr const & mvar, proof_state const & ps);
    void display_tactic_exception(tactic_exception const & ex, proof_state const & ps, expr const & pre_tac);
    optional<expr> get_pre_tactic_for(expr const & mvar);
    optional<tactic> pre_tactic_to_tactic(expr const & pre_tac);
    bool try_using(substitution & subst, expr const & mvar, proof_state const & ps,
                   expr const & pre_tac, tactic const & tac, bool show_failure);
    bool try_using_begin_end(substitution & subst, expr const & mvar, proof_state ps, expr const & pre_tac);
    void solve_unassigned_mvar(substitution & subst, expr mvar, name_set & visited);
    expr solve_unassigned_mvars(substitution & subst, expr e, name_set & visited);
    expr solve_unassigned_mvars(substitution & subst, expr const & e);
    bool display_unassigned_mvars(expr const & e, substitution const & s);
    void check_sort_assignments(substitution const & s);
    expr apply(substitution & s, expr const & e, name_set & univ_params, buffer<name> & new_params);
    std::tuple<expr, level_param_names> apply(substitution & s, expr const & e);
    elaborate_result elaborate_nested(list<expr> const & ctx, optional<expr> const & expected_type, expr const & e,
                                      bool use_tactic_hints, substitution const &, bool report_unassigned);

    expr const & get_equation_fn(expr const & eq) const;
    expr visit_equations(expr const & eqns, constraint_seq & cs);
    expr visit_equation(expr const & e, constraint_seq & cs);
    expr visit_inaccessible(expr const & e, constraint_seq & cs);
    expr visit_decreasing(expr const & e, constraint_seq & cs);
    constraint mk_equations_cnstr(expr const & m, expr const & eqns);

    bool is_structure_like(expr const & S);
    expr visit_structure_instance(expr const & e, constraint_seq & cs);

    expr process_obtain_expr(list<obtain_struct> const & s_list, list<expr> const & from_list,
                             expr const & goal, bool first, constraint_seq & cs, expr const & src);
    expr visit_obtain_expr(expr const & e, constraint_seq & cs);

    void check_used_local_tactic_hints();

    void show_goal(proof_state const & ps, expr const & start, expr const & end, expr const & curr);
public:
    elaborator(elaborator_context & ctx, name_generator && ngen, bool nice_mvar_names = false);
    std::tuple<expr, level_param_names> operator()(list<expr> const & ctx, expr const & e, bool _ensure_type);
    std::tuple<expr, expr, level_param_names> operator()(expr const & t, expr const & v, name const & n);
};

std::tuple<expr, level_param_names> elaborate(elaborator_context & env, list<expr> const & ctx, expr const & e,
                                              bool ensure_type = false, bool nice_mvar_names = false);

std::tuple<expr, expr, level_param_names> elaborate(elaborator_context & env, name const & n, expr const & t, expr const & v);
void initialize_elaborator();
void finalize_elaborator();
}
