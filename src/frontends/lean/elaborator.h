/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "kernel/pos_info_provider.h"
#include "library/local_context.h"
#include "library/type_context.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/elaborator_exception.h"

namespace lean {
class elaborator {
public:
    class checkpoint;
private:
    typedef std::vector<pair<expr, expr>> to_check_sorts;
    enum class arg_mask {
        All /* @ annotation */,
        Simple /* @@ annotation */,
        Default /* default behavior */
    };
    environment       m_env;
    options           m_opts;
    type_context      m_ctx;

    list<level>       m_uvar_stack;
    list<expr>        m_mvar_stack;
    list<expr>        m_instance_stack;
    list<expr>        m_numeral_type_stack;
    list<expr_pair>   m_tactic_stack;
    list<expr_pair>   m_inaccessible_stack;

    /* m_depth is only used for tracing */
    unsigned          m_depth{0};

    struct base_snapshot {
        metavar_context m_saved_mctx;
        list<expr>      m_saved_instance_stack;
        list<expr>      m_saved_numeral_type_stack;
        list<expr_pair> m_saved_tactic_stack;
        list<expr_pair> m_saved_inaccessible_stack;
        base_snapshot(elaborator const & elab);
        void restore(elaborator & elab);
    };

    struct snapshot : public base_snapshot {
        list<level>     m_saved_uvar_stack;
        list<expr>      m_saved_mvar_stack;
        snapshot(elaborator const & elab);
        void restore(elaborator & elab);
    };

    /** \brief We use a specialized procedure for elaborating recursor applications (e.g., nat.rec_on and eq.rec_on),
        and similar applications (e.g., eq.subst). We use the specialized procedure for f whenever the type of f is
        of the form (C a_1 ... a_n) where C and a_i's are parameters. Moreover, the parameters a_i's
        can be inferred using explicit parameters. */
    struct elim_info {
        unsigned       m_arity; /* "arity" of the "eliminator" */
        unsigned       m_nexplicit; /* Number of explicit arguments */
        unsigned       m_motive_idx; /* Position of the motive (i.e., C) */
        list<unsigned> m_explicit_idxs; /* Position of the explicit parameters that we use to synthesize the a_i's */
        elim_info() {}
        elim_info(unsigned arity, unsigned nexplicit, unsigned midx, list<unsigned> const & eidxs):
            m_arity(arity), m_nexplicit(nexplicit), m_motive_idx(midx), m_explicit_idxs(eidxs) {}
    };

    /** \brief Cache for constants that are handled using "eliminator" elaboration. */
    typedef name_map<optional<elim_info>> elim_cache;
    elim_cache        m_elim_cache;

    /* The following vector contains sorts that we should check
       whether the computed universe is too specific or not. */
    to_check_sorts    m_to_check_sorts;

    /* if m_no_info is true, we do not collect information when true,
       we set is to true whenever we find no_info annotation. */
    bool              m_no_info{true};

    bool              m_in_pattern{false};

    expr get_default_numeral_type();

    typedef std::function<format(expr const &)> pp_fn;
    pp_fn mk_pp_ctx(type_context const & ctx);
    format pp_indent(pp_fn const & pp_fn, expr const & e);
    format pp_indent(expr const & e);
    format pp_overloads(pp_fn const & pp_fn, buffer<expr> const & fns);

    expr infer_type(expr const & e) { return m_ctx.infer(e); }
    expr whnf(expr const & e) { return m_ctx.whnf(e); }
    expr try_to_pi(expr const & e) { return m_ctx.try_to_pi(e); }
    bool is_def_eq(expr const & e1, expr const & e2) { return m_ctx.is_def_eq(e1, e2); }
    bool assign_mvar(expr const & e1, expr const & e2) { lean_assert(is_metavar(e1)); return is_def_eq(e1, e2); }
    expr instantiate_mvars(expr const & e);
    bool is_uvar_assigned(level const & l) const { return m_ctx.is_assigned(l); }
    bool is_mvar_assigned(expr const & e) const { return m_ctx.is_assigned(e); }

    level mk_univ_metavar();
    expr mk_metavar(expr const & A);
    expr mk_type_metavar();
    expr mk_metavar(optional<expr> const & A);
    expr mk_instance_core(local_context const & lctx, expr const & C, expr const & ref);
    expr mk_instance_core(expr const & C, expr const & ref);
    expr mk_instance(expr const & C, expr const & ref);
    level get_level(expr const & A, expr const & ref);

    level replace_univ_placeholder(level const & l);

    void trace_coercion_failure(expr const & e_type, expr const & type, expr const & ref, char const * error_msg);
    optional<expr> mk_coercion(expr const & e, expr const & e_type, expr const & type, expr const & ref);

    void trace_coercion_fn_sort_failure(bool is_fn, expr const & e_type, expr const & ref, char const * error_msg);
    optional<expr> mk_coercion_to_fn_sort(bool is_fn, expr const & e, expr const & _e_type, expr const & ref);

    optional<expr> mk_coercion_to_fn(expr const & e, expr const & e_type, expr const & ref) {
        return mk_coercion_to_fn_sort(true, e, e_type, ref);
    }

    optional<expr> mk_coercion_to_sort(expr const & e, expr const & e_type, expr const & ref) {
        return mk_coercion_to_fn_sort(false, e, e_type, ref);
    }

    expr ensure_type(expr const & e, expr const & ref);
    expr ensure_function(expr const & e, expr const & ref);
    optional<expr> ensure_has_type(expr const & e, expr const & e_type, expr const & type, expr const & ref);
    expr enforce_type(expr const & e, expr const & expected_type, char const * header, expr const & ref);

    bool is_elim_elab_candidate(name const & fn);
    optional<elim_info> use_elim_elab_core(name const & fn);
    optional<elim_info> use_elim_elab(name const & fn);

    expr checkpoint_visit(expr const & e, optional<expr> const & expected_type);

    expr visit_typed_expr(expr const & e);
    expr visit_prenum_core(expr const & e, optional<expr> const & expected_type);
    expr visit_prenum(expr const & e, optional<expr> const & expected_type);
    expr visit_placeholder(expr const & e, optional<expr> const & expected_type);
    expr visit_have_expr(expr const & e, optional<expr> const & expected_type);
    expr visit_by(expr const & e, optional<expr> const & expected_type);
    expr visit_anonymous_constructor(expr const & e, optional<expr> const & expected_type);

    expr visit_sort(expr const & e);
    expr visit_const_core(expr const & e);
    expr ensure_function(expr const & e);
    expr visit_function(expr const & fn, bool has_args, expr const & ref);
    format mk_app_type_mismatch_error(expr const & t, expr const & arg, expr const & arg_type, expr const & expected_type);
    format mk_too_many_args_error(expr const & fn_type);
    [[ noreturn ]]
    void throw_app_type_mismatch(expr const & t, expr const & arg, expr const & arg_type, expr const & expected_type,
                                 expr const & ref);

    bool is_propagate_expected_candidate(expr const & fn);
    optional<expr> visit_app_propagate_expected(expr const & fn, buffer<expr> const & args,
                                                expr const & expected_type, expr const & ref);
    expr visit_default_app_core(expr const & fn, arg_mask amask, buffer<expr> const & args,
                                bool args_already_visited, optional<expr> const & expected_type, expr const & ref);
    expr visit_default_app(expr const & fn, arg_mask amask, buffer<expr> const & args,
                           optional<expr> const & expected_type, expr const & ref);
    void validate_overloads(buffer<expr> const & fns, expr const & ref);
    [[ noreturn ]]
    void throw_no_overload_applicable(buffer<expr> const & fns, buffer<elaborator_exception> const & error_msgs, expr const & ref);
    expr visit_overload_candidate(expr const & fn, buffer<expr> const & args,
                                  optional<expr> const & expected_type, expr const & ref);
    expr visit_overloaded_app(buffer<expr> const & fns, buffer<expr> const & args,
                              optional<expr> const & expected_type, expr const & ref);
    expr visit_elim_app(expr const & fn, elim_info const & info, buffer<expr> const & args,
                        optional<expr> const & expected_type, expr const & ref);
    expr visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type, expr const & ref);
    expr visit_local(expr const & e, optional<expr> const & expected_type);
    expr visit_constant(expr const & e, optional<expr> const & expected_type);
    expr visit_macro(expr const & e, optional<expr> const & expected_type, bool is_app_fn);
    expr visit_lambda(expr const & e, optional<expr> const & expected_type);
    expr visit_pi(expr const & e);
    expr visit_app(expr const & e, optional<expr> const & expected_type);
    expr visit_let(expr const & e, optional<expr> const & expected_type);
    expr visit_convoy(expr const & e, optional<expr> const & expected_type);
    expr visit_equations(expr const & e);
    expr visit_equation(expr const & eq);
    expr visit_inaccessible(expr const & e, optional<expr> const & expected_type);
    expr visit(expr const & e, optional<expr> const & expected_type);

    void ensure_numeral_types_assigned(checkpoint const & C);
    void synthesize_type_class_instances_core(list<expr> const & old_stack, bool force);
    void try_to_synthesize_type_class_instances(list<expr> const & old_stack) {
        synthesize_type_class_instances_core(old_stack, false);
    }
    void synthesize_type_class_instances(checkpoint const & C) {
        synthesize_type_class_instances_core(C.m_saved_instance_stack, true);
    }
    tactic_state mk_tactic_state_for(expr const & mvar);
    void invoke_tactic(expr const & mvar, expr const & tac);
    void invoke_tactics(checkpoint const & C);
    void check_inaccessible(checkpoint const & C);
    void process_checkpoint(checkpoint & C);

    void unassigned_uvars_to_params(level const & l);
    void unassigned_uvars_to_params(expr const & e);

public:
    elaborator(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx);
    metavar_context const & mctx() const { return m_ctx.mctx(); }
    local_context const & lctx() const { return m_ctx.lctx(); }
    type_context & ctx() { return m_ctx; }
    expr push_local(name const & n, expr const & type, binder_info const & bi = binder_info()) {
        return m_ctx.push_local(n, type, bi);
    }
    expr elaborate(expr const & e);
    expr elaborate_type(expr const & e);
    expr_pair elaborate_with_type(expr const & e, expr const & e_type);
    void ensure_no_unassigned_metavars(expr const & e);
    /**
       \brief Finalize all expressions in \c es.
       es is input and output, all expr fragments at once.

       The finalization includes:
       1- Assigning unassigned universe metavariables to fresh parameters.
       2- Throwing an error if any of \c es contains an unassigned (regular) metavariable when check_unassigned = true
       3- Substituting assigned metavariables in \c es.
       4- Converting unassigned metavariable refs (i.e., the ones managed by metavar_context) into kernel
          metavariables.

       \remark new_lp_names is output only, and contains one fresh universe parameter for each unassigned universe
       meta-variable. */
    void finalize(buffer<expr> & es, buffer<name> & new_lp_names, bool check_unassigned, bool to_simple_metavar);
    /** Simpler version of \c finalize, where \c es contains only one expression. */
    pair<expr, level_param_names> finalize(expr const & e, bool check_unassigned, bool to_simple_metavar);
    environment const & env() const { return m_env; }

    class checkpoint : public base_snapshot {
        elaborator & m_elaborator;
        bool         m_commit;
    public:
        checkpoint(elaborator & e);
        ~checkpoint();
        void commit();
        void process() { m_elaborator.process_checkpoint(*this); }
    };
};

pair<expr, level_param_names> elaborate(environment & env, options const & opts,
                                        metavar_context & mctx, local_context const & lctx,
                                        expr const & e, bool check_unassigend);

expr nested_elaborate(environment & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                      expr const & e, bool relaxed);

void initialize_elaborator();
void finalize_elaborator();
}
