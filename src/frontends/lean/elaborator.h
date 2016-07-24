/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
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

    /* The following vector contains sorts that we should check
       whether the computed universe is too specific or not. */
    to_check_sorts    m_to_check_sorts;

    /* if m_no_info is true, we do not collect information when true,
       we set is to true whenever we find no_info annotation. */
    bool              m_no_info{true};

    expr get_default_numeral_type();

    format pp(expr const & e);
    format pp_indent(expr const & e);

    expr infer_type(expr const & e) { return m_ctx.infer(e); }
    bool is_def_eq(expr const & e1, expr const & e2) { return m_ctx.is_def_eq(e1, e2); }
    bool assign_mvar(expr const & e1, expr const & e2) { lean_assert(is_metavar(e1)); return is_def_eq(e1, e2); }
    expr instantiate_mvars(expr const & e) { return m_ctx.instantiate_mvars(e); }
    bool is_uvar_assigned(level const & l) const { return m_ctx.is_assigned(l); }
    bool is_mvar_assigned(expr const & e) const { return m_ctx.is_assigned(e); }
    void resolve_instances_from(unsigned old_sz);

    level mk_univ_metavar();
    expr mk_metavar(expr const & A);
    expr mk_type_metavar();
    expr mk_instance(expr const & C);
    level get_level(expr const & A);

    level replace_univ_placeholder(level const & l);

    expr ensure_type(expr const & e, expr const & ref);
    expr ensure_has_type(expr const & e, expr const & type, expr const & ref);
    expr ensure_function(expr const & e, expr const & ref);

    expr visit_typed_expr(expr const & e);
    expr visit_prenum_core(expr const & e, optional<expr> const & expected_type);
    expr visit_prenum(expr const & e, optional<expr> const & expected_type);

    expr visit_sort(expr const & e);
    expr visit_const_core(expr const & e);
    expr ensure_function(expr const & e);
    expr visit_function(expr const & fn, bool has_args, expr const & ref);
    void filter_using_arity(buffer<expr> & fn, arg_mask amask, unsigned num_args);
    expr visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type);
    expr visit_local(expr const & e, optional<expr> const & expected_type);
    expr visit_constant(expr const & e, optional<expr> const & expected_type);
    expr visit_macro(expr const & e, optional<expr> const & expected_type);
    expr visit_lambda(expr const & e, optional<expr> const & expected_type);
    expr visit_pi(expr const & e, optional<expr> const & expected_type);
    expr visit_app(expr const & e, optional<expr> const & expected_type);
    expr visit_let(expr const & e, optional<expr> const & expected_type);
    expr visit(expr const & e, optional<expr> const & expected_type);

public:
    elaborator(environment const & env, options const & opts, local_level_decls const & lls,
               metavar_context const & mctx, local_context const & lctx);

    std::tuple<expr, level_param_names> operator()(expr const & e);
};

std::tuple<expr, level_param_names> elaborate(environment const & env, options const & opts, local_level_decls const & lls,
                                              metavar_context const & mctx, local_context const & lctx, expr const & e);
}
