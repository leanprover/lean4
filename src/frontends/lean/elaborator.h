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
#include "library/context_cache.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/elaborator_exception.h"
#include "frontends/lean/info_manager.h"
#include "library/sorry.h"

namespace lean {
enum class elaborator_strategy {
    Simple,
    WithExpectedType,
    AsEliminator
};

struct sanitize_param_names_fn;

class elaborator {
public:
    class checkpoint;
private:
    friend class validate_and_collect_lhs_mvars;
    friend class visit_structure_instance_fn;
    typedef std::vector<pair<expr, expr>> to_check_sorts;
    enum class arg_mask {
        AllExplicit /* @ annotation */,
        InstHoExplicit, /* @@ annotation (i.e., instance implicit and higher-order arguments are explicit  */
        Default /* default behavior */
    };
    environment       m_env;
    options           m_opts;
    context_cache     m_cache;
    name              m_decl_name;
    type_context_old      m_ctx;
    info_manager      m_info;
    unsigned          m_aux_meta_idx = 1;
    bool              m_recover_from_errors;
    bool              m_has_errors = false;

    list<expr>        m_instances;
    list<expr>        m_numeral_types;
    list<expr_pair>   m_tactics;
    list<expr_pair>   m_holes;

    /* m_depth is only used for tracing */
    unsigned          m_depth{0};

    bool              m_uses_infom;
    bool              m_coercions;

    struct snapshot {
        metavar_context        m_saved_mctx;
        info_manager           m_saved_info;
        list<expr>             m_saved_instances;
        list<expr>             m_saved_numeral_types;
        list<expr_pair>        m_saved_tactics;
        list<expr_pair>        m_saved_holes;

        snapshot(elaborator const & elab);
        void restore(elaborator & elab);
    };

    /** \brief We use a specialized procedure for elaborating recursor applications (e.g., nat.rec_on and eq.rec_on),
        and similar applications (e.g., eq.subst). We use the specialized procedure for f whenever the type of f is
        of the form (C a_1 ... a_n) where C and a_i's are parameters. Moreover, the parameters a_i's
        can be inferred using explicit parameters. */
    struct elim_info {
        unsigned       m_arity;      /* "arity" of the "eliminator" */
        unsigned       m_nexplicit;  /* Number of explicit arguments */
        unsigned       m_motive_idx; /* Position of the motive (i.e., C) */
        list<unsigned> m_idxs;       // Position of the explicit parameters that we use to synthesize the a_i's
                                     // or need to be processed in the first pass.
        elim_info() {}
        elim_info(unsigned arity, unsigned nexplicit, unsigned midx, list<unsigned> const & idxs):
            m_arity(arity), m_nexplicit(nexplicit), m_motive_idx(midx), m_idxs(idxs) {}
    };

    /** \brief Cache for constants that are handled using "eliminator" elaboration. */
    typedef name_map<optional<elim_info>> elim_cache;
    typedef name_map<format>              elim_failure_info;
    elim_cache        m_elim_cache;
    elim_failure_info m_elim_failure_info;

    /* The following vector contains sorts that we should check
       whether the computed universe is too specific or not. */
    to_check_sorts    m_to_check_sorts;

    /* if m_no_info is true, we do not collect information when true,
       we set is to true whenever we find no_info annotation. */
    bool              m_no_info{false};

    bool              m_in_pattern{false};
    bool              m_in_quote{false};

    expr get_default_numeral_type();

    typedef std::function<format(expr const &)> pp_fn;
    pp_fn mk_pp_ctx();
    formatter mk_fmt_ctx();
    format pp_indent(pp_fn const & pp_fn, expr const & e);
    format pp_indent(expr const & e);
    format pp(expr const & e);
    format pp_overload(pp_fn const & pp_fn, expr const & fn);
    format pp_overloads(pp_fn const & pp_fn, buffer<expr> const & fns);
    format pp_type_mismatch(expr const & e, expr const & e_type, expr const & expected_type);
    format pp_type_mismatch(expr const & e_type, expr const & expected_type);
    expr whnf(expr const & e) { return m_ctx.whnf(e); }
    expr try_to_pi(expr const & e) { return m_ctx.try_to_pi(e); }
    bool is_def_eq(expr const & e1, expr const & e2);
    bool try_is_def_eq(expr const & e1, expr const & e2);
    bool is_uvar_assigned(level const & l) const { return m_ctx.is_assigned(l); }
    bool is_mvar_assigned(expr const & e) const { return m_ctx.is_assigned(e); }

    expr push_local(type_context_old::tmp_locals & locals, name const & n, expr const & type,
                    binder_info const & binfo, expr const & ref);
    expr push_let(type_context_old::tmp_locals & locals,
                  name const & n, expr const & type, expr const & value, expr const & ref);

    level mk_univ_metavar();
    expr mk_metavar(expr const & A, expr const & ref);
    expr mk_metavar(name const & pp_n, expr const & A, expr const & ref);
    expr mk_type_metavar(expr const & ref);
    expr mk_metavar(optional<expr> const & A, expr const & ref);
    expr mk_instance_core(local_context const & lctx, expr const & C, expr const & ref);
    expr mk_instance_core(expr const & C, expr const & ref);
    expr mk_instance(expr const & C, expr const & ref);
    level get_level(expr const & A, expr const & ref);

    level replace_univ_placeholder(level const & l);

    void trace_coercion_failure(expr const & e_type, expr const & type, expr const & ref, char const * error_msg);
    optional<expr> mk_Prop_to_bool_coercion(expr const & e, expr const & ref);
    optional<expr> mk_coercion_core(expr const & e, expr const & e_type, expr const & type, expr const & ref);
    bool is_monad(expr const & e);
    bool is_monad_fail(expr const & e);
    optional<expr> try_monad_coercion(expr const & e, expr const & e_type, expr type, expr const & ref);
    optional<expr> mk_coercion(expr const & e, expr e_type, expr type, expr const & ref);

    void trace_coercion_fn_sort_failure(bool is_fn, expr const & e_type, expr const & ref, char const * error_msg);
    optional<expr> mk_coercion_to_fn_sort(bool is_fn, expr const & e, expr const & _e_type, expr const & ref);

    optional<expr> mk_coercion_to_fn(expr const & e, expr const & e_type, expr const & ref) {
        return mk_coercion_to_fn_sort(true, e, e_type, ref);
    }

    optional<expr> mk_coercion_to_sort(expr const & e, expr const & e_type, expr const & ref) {
        return mk_coercion_to_fn_sort(false, e, e_type, ref);
    }

    bool has_synth_sorry(expr const & e) { return has_synth_sorry({e}); }
    bool has_synth_sorry(std::initializer_list<expr> && es);

public:
    bool try_report(std::exception const & ex);
    bool try_report(std::exception const & ex, optional<expr> const & ref);
    void report_or_throw(elaborator_exception const & ex);
    expr mk_sorry(expr const & type, bool synthetic = true) { return ::lean::mk_sorry(type, synthetic); }
    expr mk_sorry(optional<expr> const & expected_type, expr const & ref, bool synthetic = true);
    expr recoverable_error(optional<expr> const & expected_type, expr const & ref, elaborator_exception const & ex);
    template <class Fn> expr recover_expr_from_exception(optional<expr> const & expected_type, expr const & ref, Fn &&);

private:
    expr ensure_type(expr const & e, expr const & ref);
    expr ensure_function(expr const & e, expr const & ref);
    optional<expr> ensure_has_type(expr const & e, expr const & e_type, expr const & type, expr const & ref);
    expr enforce_type(expr const & e, expr const & expected_type, char const * header, expr const & ref);

    bool is_elim_elab_candidate(name const & fn);
    elim_info get_elim_info_for_builtin(name const & fn);
    optional<elim_info> use_elim_elab_core(name const & fn);
    optional<elim_info> use_elim_elab(name const & fn);

    expr strict_visit(expr const & e, optional<expr> const & expected_type);

    expr visit_scope_trace(expr const & e, optional<expr> const & expected_type);
    expr visit_typed_expr(expr const & e);
    level dec_level(level const & l, expr const & ref);
    expr visit_prenum(expr const & e, optional<expr> const & expected_type);
    expr visit_placeholder(expr const & e, optional<expr> const & expected_type);
    expr visit_have_expr(expr const & e, optional<expr> const & expected_type);
    expr visit_suffices_expr(expr const & e, optional<expr> const & expected_type);
    expr visit_by(expr const & e, optional<expr> const & expected_type);
    expr visit_hole(expr const & e, optional<expr> const & expected_type);
    expr visit_anonymous_constructor(expr const & e, optional<expr> const & expected_type);
    expr visit_emptyc_or_emptys(expr const & e, optional<expr> const & expected_type);

    expr visit_sort(expr const & e);
    expr visit_const_core(expr const & e);
    void save_identifier_info(expr const & f);
    expr visit_function(expr const & fn, bool has_args, optional<expr> const & expected_type, expr const & ref);
    [[noreturn]] void throw_app_type_mismatch_error(expr const & t, expr const & arg, expr const & arg_type,
                                                    expr const & expected_type, expr const & ref);
    format mk_app_arg_mismatch_error(expr const & t, expr const & arg, expr const & expected_arg);

    bool is_with_expected_candidate(expr const & fn);
    std::tuple<expr, expr, optional<expr>> elaborate_arg(expr const & arg, expr const & expected_type, expr const & ref);
    expr post_process_implicit_arg(expr const & arg, expr const & ref);
    struct first_pass_info;
    void first_pass(expr const & fn, buffer<expr> const & args, expr const & expected_type, expr const & ref,
                    first_pass_info & info);
    expr second_pass(expr const & fn, buffer<expr> const & args, expr const & ref, first_pass_info & info);
    expr visit_base_app_simple(expr const & _fn, arg_mask amask, buffer<expr> const & args,
                               bool args_already_visited, optional<expr> const & expected_type, expr const & ref);
    expr visit_base_app_core(expr const & fn, arg_mask amask, buffer<expr> const & args,
                             bool args_already_visited, optional<expr> const & expected_type, expr const & ref);
    expr visit_base_app(expr const & fn, arg_mask amask, buffer<expr> const & args,
                        optional<expr> const & expected_type, expr const & ref);
    void validate_overloads(buffer<expr> const & fns, expr const & ref);
    format mk_no_overload_applicable_msg(buffer<expr> const & fns, buffer<elaborator_exception> const & error_msgs);
    expr visit_overload_candidate(expr const & fn, buffer<expr> const & args,
                                  optional<expr> const & expected_type, expr const & ref);
    expr visit_overloaded_app_with_expected(buffer<expr> const & fns, buffer<expr> const & args,
                                            expr const & expected_type, expr const & ref);
    expr visit_overloaded_app_core(buffer<expr> const & fns, buffer<expr> const & args,
                                   optional<expr> const & expected_type, expr const & ref);
    expr visit_overloaded_app(buffer<expr> const & fns, buffer<expr> const & args,
                              optional<expr> const & expected_type, expr const & ref);
    expr visit_elim_app(expr const & fn, elim_info const & info, buffer<expr> const & args,
                        optional<expr> const & expected_type, expr const & ref);
    expr visit_no_confusion_app(expr const & fn, buffer<expr> const & args, optional<expr> const & expected_type,
                                expr const & ref);
    expr visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type, expr const & ref);
    expr visit_local(expr const & e, optional<expr> const & expected_type);
    expr visit_constant(expr const & e, optional<expr> const & expected_type);
    expr visit_macro(expr const & e, optional<expr> const & expected_type, bool is_app_fn);
    expr visit_lambda(expr const & e, optional<expr> const & expected_type);
    expr visit_pi(expr const & e);
    expr visit_app(expr const & e, optional<expr> const & expected_type);
    expr visit_let(expr const & e, optional<expr> const & expected_type);
    expr visit_convoy(expr const & e, optional<expr> const & expected_type);
    bool keep_do_failure_eq(expr const & first_eq);
    expr visit_equations(expr const & e);
    expr visit_equation(expr const & eq, unsigned num_fns);
    expr visit_inaccessible(expr const & e, optional<expr> const & expected_type);

    struct field_resolution {
        name m_S_name; // structure name of field expression type
        name m_base_S_name; // structure name of field
        name m_fname;
        optional<local_decl> m_ldecl; // projection is a local constant: recursive call

        field_resolution(name const & full_fname, optional<local_decl> ldecl = {}):
                m_S_name(full_fname.get_prefix()), m_base_S_name(full_fname.get_prefix()),
                m_fname(full_fname.get_string()), m_ldecl(ldecl) {}
        field_resolution(const name & S_name, const name & base_S_name, const name & fname):
                m_S_name(S_name), m_base_S_name(base_S_name), m_fname(fname) {}

        name get_full_fname() const { return m_base_S_name + m_fname; }
    };

    field_resolution field_to_decl(expr const & e, expr const & s, expr const & s_type);
    field_resolution find_field_fn(expr const & e, expr const & s, expr const & s_type);
    expr visit_field(expr const & e, optional<expr> const & expected_type);
    expr instantiate_mvars(expr const & e, std::function<bool(expr const &)> pred); // NOLINT
    expr visit_structure_instance(expr const & e, optional<expr> expected_type);
    expr visit_expr_quote(expr const & e, optional<expr> const & expected_type);
    expr visit(expr const & e, optional<expr> const & expected_type);

    tactic_state mk_tactic_state_for(expr const & mvar);
    void invoke_tactic(expr const & mvar, expr const & tac);

    bool ready_to_synthesize(expr inst_type);

    void process_hole(expr const & mvar, expr const & arg);
    void process_holes();

    bool synthesize_type_class_instance_core(expr const & mvar, expr const & inferred_inst, expr const & inst_type);
    bool try_synthesize_type_class_instance(expr const & mvar);
    void synthesize_numeral_types();
    void synthesize_type_class_instances_step();
    void synthesize_type_class_instances();
    void synthesize_using_tactics();
    void synthesize_no_tactics();
    void synthesize();

    void finalize_core(sanitize_param_names_fn & S, buffer<expr> & es,
                       bool check_unassigned, bool to_simple_metavar, bool collect_local_ctx);

    expr mk_auto_param(expr const & name_lit, expr const & expected_type, expr const & ref);
    optional<expr> process_optional_and_auto_params(expr type, expr const & ref, buffer<expr> & eta_args, buffer<expr> & new_args);

    expr mk_aux_meta_def(expr const & e, expr const & ref);

public:
    elaborator(environment const & env, options const & opts, name const & decl_name,
               metavar_context const & mctx, local_context const & lctx,
               bool recover_from_errors = true, bool in_pattern = false, bool in_quote = false);
    ~elaborator();
    abstract_context_cache & get_cache() { return m_cache; }
    metavar_context const & mctx() const { return m_ctx.mctx(); }
    local_context const & lctx() const { return m_ctx.lctx(); }
    environment const & env() const { return m_env; }
    options const & get_options() const { return m_opts; }
    void set_env(environment const & env) {
        m_env = env;
        m_ctx.set_env(m_env);
    }

    expr push_local(name const & n, expr const & type, binder_info const & bi = binder_info()) {
        return m_ctx.push_local(n, type, bi);
    }
    expr mk_pi(buffer<expr> const & params, expr const & type) { return m_ctx.mk_pi(params, type); }
    expr mk_lambda(buffer<expr> const & params, expr const & type) { return m_ctx.mk_lambda(params, type); }
    expr infer_type(expr const & e) { return m_ctx.infer(e); }
    expr instantiate_mvars(expr const & e);
    void freeze_local_instances() { m_ctx.freeze_local_instances(); }
    expr elaborate(expr const & e);
    expr elaborate_type(expr const & e);
    expr_pair elaborate_with_type(expr const & e, expr const & e_type);
    void report_error(tactic_state const & s, char const * state_header,
                      char const * msg, expr const & ref);
    void ensure_no_unassigned_metavars(expr & e);
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

    /* We finalize theorem in two steps: type, and then its proof.
       We use theorem_finalization_info to communicate information from the first step to the second. */
    struct theorem_finalization_info {
        name_set        m_L;
    };
    pair<expr, theorem_finalization_info> finalize_theorem_type(expr const & type, buffer<name> & new_lp_names);
    expr finalize_theorem_proof(expr const & val, theorem_finalization_info const & info);

    bool has_errors() const { return m_has_errors; }
};

template <class Fn>
expr elaborator::recover_expr_from_exception(optional<expr> const & expected_type, expr const & ref, Fn && fn) {
    try {
        return fn();
    } catch (std::exception & ex) {
        if (!try_report(ex, some_expr(ref))) {
            throw;
        } else {
            return mk_sorry(expected_type, ref);
        }
    }
}

pair<expr, level_param_names> elaborate(environment & env, options const & opts, name const & decl_name,
                                        metavar_context & mctx, local_context const & lctx,
                                        expr const & e, bool check_unassigned, bool recover_from_errors);

/** \brief Translated local constants (and undefined constants) occurring in \c e into
    local constants provided by \c ctx.
    Throw exception is \c ctx does not contain the local constant. */
expr resolve_names(environment const & env, local_context const & lctx, expr const & e);

void initialize_elaborator();
void finalize_elaborator();
}
