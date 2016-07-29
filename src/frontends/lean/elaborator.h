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
#include "frontends/lean/elaborator_context.h"

namespace lean {
class elaborator {
    typedef std::vector<pair<expr, expr>> to_check_sorts;
    enum class arg_mask {
        All /* @ annotation */,
        Simple /* @@ annotation */,
        Default /* default behavior */
    };
    environment       m_env;
    options           m_opts;
    local_level_decls m_local_level_decls;
    type_context      m_ctx;

    buffer<level>     m_uvar_stack;
    buffer<expr>      m_mvar_stack;
    buffer<expr>      m_instance_stack;
    buffer<expr>      m_numeral_type_stack;

    struct checkpoint {
        elaborator & m_elaborator;
        bool         m_commit;
        unsigned     m_uvar_stack_sz;
        unsigned     m_mvar_stack_sz;
        unsigned     m_instance_stack_sz;
        unsigned     m_numeral_type_stack_sz;
        checkpoint(elaborator & e);
        ~checkpoint();
        void commit();
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

    expr get_default_numeral_type();

    format pp(type_context & ctx, expr const & e);
    format pp(expr const & e);
    format pp_indent(type_context & ctx, expr const & e);
    format pp_indent(expr const & e);
    format pp_overloads(buffer<expr> const & fns);
    format pp(local_context const & lctx);

    expr infer_type(expr const & e) { return m_ctx.infer(e); }
    expr whnf(expr const & e) { return m_ctx.whnf(e); }
    expr try_to_pi(expr const & e) { return m_ctx.try_to_pi(e); }
    bool is_def_eq(expr const & e1, expr const & e2) { return m_ctx.is_def_eq(e1, e2); }
    bool assign_mvar(expr const & e1, expr const & e2) { lean_assert(is_metavar(e1)); return is_def_eq(e1, e2); }
    expr instantiate_mvars(expr const & e);
    bool is_uvar_assigned(level const & l) const { return m_ctx.is_assigned(l); }
    bool is_mvar_assigned(expr const & e) const { return m_ctx.is_assigned(e); }
    void resolve_instances_from(unsigned old_sz);

    level mk_univ_metavar();
    expr mk_metavar(expr const & A);
    expr mk_type_metavar();
    expr mk_instance_core(local_context const & lctx, expr const & C);
    expr mk_instance_core(expr const & C);
    expr mk_instance(expr const & C);
    level get_level(expr const & A);

    level replace_univ_placeholder(level const & l);

    expr ensure_type(expr const & e, expr const & ref);
    expr ensure_function(expr const & e, expr const & ref);
    optional<expr> ensure_has_type(expr const & e, expr const & e_type, expr const & type);
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

    expr visit_sort(expr const & e);
    expr visit_const_core(expr const & e);
    expr ensure_function(expr const & e);
    expr visit_function(expr const & fn, bool has_args, expr const & ref);
    format mk_app_type_mismatch_error(expr const & t, expr const & arg, expr const & arg_type, expr const & expected_type);
    format mk_too_many_args_error(expr const & fn_type);
    void throw_app_type_mismatch(expr const & t, expr const & arg, expr const & arg_type, expr const & expected_type,
                                 expr const & ref);
    expr visit_default_app_core(expr const & fn, arg_mask amask, buffer<expr> const & args,
                                bool args_already_visited, optional<expr> const & expected_type, expr const & ref);
    expr visit_default_app(expr const & fn, arg_mask amask, buffer<expr> const & args,
                           optional<expr> const & expected_type, expr const & ref);
    void validate_overloads(buffer<expr> const & fns, expr const & ref);
    expr visit_overload_candidate(expr const & fn, buffer<expr> const & args,
                                  optional<expr> const & expected_type, expr const & ref);
    expr visit_overloaded_app(buffer<expr> const & fns, buffer<expr> const & args,
                              optional<expr> const & expected_type, expr const & ref);
    expr visit_elim_app(expr const & fn, elim_info const & info, buffer<expr> const & args,
                        optional<expr> const & expected_type, expr const & ref);
    expr visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type, expr const & ref);
    expr visit_local(expr const & e, optional<expr> const & expected_type);
    expr visit_constant(expr const & e, optional<expr> const & expected_type);
    expr visit_macro(expr const & e, optional<expr> const & expected_type);
    expr visit_lambda(expr const & e, optional<expr> const & expected_type);
    expr visit_pi(expr const & e);
    expr visit_app(expr const & e, optional<expr> const & expected_type);
    expr visit_let(expr const & e, optional<expr> const & expected_type);
    expr visit(expr const & e, optional<expr> const & expected_type);

    void ensure_numeral_types_assigned(checkpoint const & C);
    void synthesize_type_class_instances_core(unsigned old_sz, bool force);
    void try_to_synthesize_type_class_instances(unsigned old_sz) {
        synthesize_type_class_instances_core(old_sz, false);
    }
    void synthesize_type_class_instances(checkpoint const & C) {
        synthesize_type_class_instances_core(C.m_instance_stack_sz, true);
    }
    void invoke_tactics(checkpoint const & C);
    void ensure_no_unassigned_metavars(checkpoint const & C);
    void process_checkpoint(checkpoint const & C);

public:
    elaborator(environment const & env, options const & opts, local_level_decls const & lls,
               metavar_context const & mctx, local_context const & lctx);
    metavar_context const & mctx() const { return m_ctx.mctx(); }
    std::tuple<expr, level_param_names> operator()(expr const & e);
};

std::tuple<expr, level_param_names> elaborate(environment const & env, options const & opts, local_level_decls const & lls,
                                              metavar_context & mctx, local_context const & lctx, expr const & e);

void initialize_elaborator();
void finalize_elaborator();
}
