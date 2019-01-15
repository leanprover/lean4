/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <vector>
#include "library/placeholder.h"
#include "library/time_task.h"
#include "library/profiling.h"
#include "library/sorry.h"
#include "util/timeit.h"
#include "kernel/declaration.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/explicit.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/module.h"
#include "library/aux_definition.h"
#include "library/scope_pos_info_provider.h"
#include "library/replace_visitor.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/equations.h"
#include "library/compiler/compiler.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/util.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/definition_cmds.h"
#include "frontends/lean/typed_expr.h"

namespace lean {
environment ensure_decl_namespaces(environment const & env, name const & full_n) {
    if (full_n.is_atomic())
        return env;
    return add_namespace(env, full_n.get_prefix());
}

expr parse_equation_lhs(parser & p, expr const & fn, buffer<expr> & locals) {
    auto lhs_pos = p.pos();
    buffer<expr> lhs_args;
    lhs_args.push_back(p.parse_pattern_or_expr(get_max_prec()));
    while (!p.curr_is_token(get_assign_tk())) {
        auto pos0 = p.pos();
        lhs_args.push_back(p.parse_pattern_or_expr(get_max_prec()));
        if (p.pos() == pos0) break;
    }
    expr lhs = p.mk_app(p.save_pos(mk_explicit(fn), lhs_pos), lhs_args, lhs_pos);
    bool skip_main_fn = true;
    return p.patexpr_to_pattern(lhs, skip_main_fn, locals);
}

expr parse_equation(parser & p, expr const & fn) {
    p.check_token_next(get_bar_tk(), "invalid equation, '|' expected");
    buffer<expr> locals;
    expr lhs = parse_equation_lhs(p, fn, locals);
    auto assign_pos = p.pos();
    p.check_token_next(get_assign_tk(), "invalid equation, ':=' expected");
    expr rhs = p.parse_scoped_expr(locals);
    return Fun(locals, p.save_pos(mk_equation(lhs, rhs), assign_pos), p);
}

optional<expr> parse_using_well_founded(parser & p) {
    if (p.curr_is_token(get_using_well_founded_tk())) {
        parser::local_scope _(p);
        p.clear_expr_fvars();
        p.next();
        return some_expr(p.parse_expr(get_max_prec()));
    } else {
        return none_expr();
    }
}

expr mk_equations(parser & p, buffer<expr> const & fns,
                  buffer<name> const & fn_full_names, buffer<name> const & fn_prv_names, buffer<expr> const & eqs,
                  optional<expr> const & wf_tacs, pos_info const & pos) {
    buffer<expr> new_eqs;
    for (expr const & eq : eqs) {
        new_eqs.push_back(Fun(fns, eq, p));
    }
    equations_header h = mk_equations_header(names(fn_full_names), names(fn_prv_names));
    if (wf_tacs) {
        return p.save_pos(mk_equations(h, new_eqs.size(), new_eqs.data(), *wf_tacs), pos);
    } else {
        return p.save_pos(mk_equations(h, new_eqs.size(), new_eqs.data()), pos);
    }
}

expr mk_equations(parser & p, expr const & fn, name const & full_name, name const & full_prv_name, buffer<expr> const & eqs,
                  optional<expr> const & wf_tacs, pos_info const & pos) {
    buffer<expr> fns; fns.push_back(fn);
    buffer<name> full_names; full_names.push_back(full_name);
    buffer<name> full_prv_names; full_prv_names.push_back(full_prv_name);
    return mk_equations(p, fns, full_names, full_prv_names, eqs, wf_tacs, pos);
}

void check_valid_end_of_equations(parser & p) {
    if (!p.curr_is_command() && !p.curr_is_eof() &&
        p.curr() != token_kind::DocBlock &&
        p.curr() != token_kind::ModDocBlock &&
        !p.curr_is_token(get_with_tk()) &&
        !p.curr_is_token(get_period_tk())) {
        p.maybe_throw_error({"invalid equations, must be followed by a command, '.', 'with', doc-string or EOF", p.pos()});
    }
}

static expr parse_mutual_definition(parser & p, buffer<name> & lp_names, buffer<expr> & fns, buffer<name> & prv_names,
                                    buffer<expr> & params) {
    parser::local_scope scope1(p);
    auto header_pos = p.pos();
    buffer<expr> pre_fns;
    parse_mutual_header(p, lp_names, pre_fns, params);
    buffer<expr> eqns;
    buffer<name> full_names;
    buffer<name> full_actual_names;
    for (expr const & pre_fn : pre_fns) {
        // TODO(leo, dhs): make use of attributes
        expr fn_type = parse_inner_header(p, local_pp_name_p(pre_fn)).first;
        declaration_name_scope scope2(local_pp_name_p(pre_fn));
        declaration_name_scope scope3("_main");
        full_names.push_back(scope3.get_name());
        full_actual_names.push_back(scope3.get_actual_name());
        prv_names.push_back(scope2.get_actual_name());
        if (p.curr_is_token(get_period_tk())) {
            auto period_pos = p.pos();
            p.next();
            eqns.push_back(p.save_pos(mk_no_equation(), period_pos));
        } else {
            while (p.curr_is_token(get_bar_tk())) {
                eqns.push_back(parse_equation(p, pre_fn));
            }
            check_valid_end_of_equations(p);
        }
        expr fn      = mk_local(local_name_p(pre_fn), local_pp_name_p(pre_fn), fn_type, mk_rec_info());
        fns.push_back(fn);
    }
    if (p.curr_is_token(get_with_tk()))
        p.maybe_throw_error({"unexpected 'with' clause", p.pos()});
    optional<expr> wf_tacs = parse_using_well_founded(p);
    for (expr & eq : eqns) {
        eq = replace_locals_preserving_pos_info(eq, pre_fns, fns);
    }
    expr r = mk_equations(p, fns, full_names, full_actual_names, eqns, wf_tacs, header_pos);
    collect_implicit_locals(p, lp_names, params, r);
    return r;
}

static void finalize_definition(elaborator & elab, buffer<expr> const & params, expr & type,
                                expr & val, buffer<name> & lp_names) {
    type = elab.mk_pi(params, type);
    val  = elab.mk_lambda(params, val);
    buffer<expr> type_val;
    buffer<name> implicit_lp_names;
    type_val.push_back(type);
    type_val.push_back(val);
    elab.finalize(type_val, implicit_lp_names, true, false);
    type = type_val[0];
    val  = type_val[1];
    lp_names.append(implicit_lp_names);
}

static environment compile_decl(parser & p, environment const & env,
                                name const & c_name, name const & c_real_name, pos_info const & pos) {
    try {
        time_task _("compilation", p.mk_message(message_severity::INFORMATION), c_real_name);
        return compile(env, p.get_options(), c_real_name);
    } catch (exception & ex) {
        // FIXME(gabriel): use position from exception
        auto out = p.mk_message(pos, WARNING);
        out << "failed to generate bytecode for '" << c_name << "'\n";
        out.set_exception(ex);
        out.report();
        return env;
    }
}

static pair<environment, name>
declare_definition(parser & p, environment const & env, decl_cmd_kind kind, buffer<name> const & lp_names,
                   name const & c_name, name const & prv_name, expr type, optional<expr> val, cmd_meta const & meta,
                   bool is_abbrev, pos_info const & pos) {
    name c_real_name;
    environment new_env = env;
    if (has_private_prefix(new_env, prv_name)) {
        new_env     = register_private_name(new_env, c_name, prv_name);
        c_real_name = prv_name;
    } else {
        c_real_name = get_namespace(env) + c_name;
    }
    if (env.find(c_real_name)) {
        throw exception(sstream() << "invalid definition, a declaration named '" << c_real_name << "' has already been declared");
    }
    if (val && !meta.m_modifiers.m_is_meta && !type_checker(env).is_prop(type)) {
        /* We only abstract nested proofs if the type of the definition is not a proposition */
        std::tie(new_env, type) = abstract_nested_proofs(new_env, c_real_name, type);
        std::tie(new_env, *val) = abstract_nested_proofs(new_env, c_real_name, *val);
    }
    bool is_meta      = meta.m_modifiers.m_is_meta;
    auto def          =
        (kind == decl_cmd_kind::Theorem ?
         mk_theorem(c_real_name, names(lp_names), type, *val) :
         (is_abbrev ? mk_definition(c_real_name, names(lp_names), type, *val, reducibility_hints::mk_abbreviation(), is_meta) :
          mk_definition(new_env, c_real_name, names(lp_names), type, *val, is_meta)));
    new_env           = module::add(new_env, def);

    if (meta.m_modifiers.m_is_protected)
        new_env = add_protected(new_env, c_real_name);

    new_env = add_alias(new_env, meta.m_modifiers.m_is_protected, c_name, c_real_name);

    if (!meta.m_modifiers.m_is_private) {
        new_env = ensure_decl_namespaces(new_env, c_real_name);
    }

    if (!meta.m_modifiers.m_is_noncomputable)
        new_env = compile_decl(p, new_env, c_name, c_real_name, pos);
    return mk_pair(new_env, c_real_name);
}

static environment elab_defs_core(parser & p, decl_cmd_kind kind, cmd_meta const & meta, buffer <name> lp_names, buffer <expr> const & fns,
                           buffer <name> const & prv_names, buffer <expr> const & params, expr val, pos_info const & header_pos) {
    /* TODO(Leo): allow a different doc string for each function in a mutual definition. */
    optional<std::string> doc_string = meta.m_doc_string;
    environment env = p.env();

    // skip elaboration of definitions during reparsing
    if (p.get_break_at_pos())
        return p.env();

    bool recover_from_errors = true;
    elaborator elab(env, p.get_options(), get_namespace(env) + local_pp_name_p(fns[0]), metavar_context(), local_context(), recover_from_errors);
    buffer<expr> new_params;
    elaborate_params(elab, params, new_params);
    val = replace_locals_preserving_pos_info(val, params, new_params);
    val = elab.elaborate(val);
    if (!is_equations_result(val)) {
        /* Failed to elaborate mutual recursion.
           TODO(Leo): better error recovery. */
        return p.env();
    }
    unsigned num_defs = get_equations_result_size(val);
    lean_assert(num_defs == prv_names.size());
    lean_assert(fns.size() == num_defs);
    buffer<name> new_d_names;
    /* Define functions */
    for (unsigned i = 0; i < num_defs; i++) {
        expr curr      = get_equations_result(val, i);
        expr curr_type = head_beta_reduce(elab.infer_type(curr));
        finalize_definition(elab, new_params, curr_type, curr, lp_names);
        environment env = elab.env();
        name c_name = local_name_p(fns[i]);
        name c_real_name;
        bool is_abbrev = false;
        std::tie(env, c_real_name) = declare_definition(p, env, kind, lp_names, c_name, prv_names[i],
                                                        curr_type, some_expr(curr), meta, is_abbrev, header_pos);
        env = add_local_ref(p, env, c_name, c_real_name, lp_names, params);
        new_d_names.push_back(c_real_name);
        elab.set_env(env);
    }
    /* Apply attributes last so that they may access any information on the new decl */
    for (auto const & c_real_name : new_d_names) {
        elab.set_env(meta.m_attrs.apply(elab.env(), p.ios(), c_real_name));
    }
    return elab.env();
}

static environment mutual_definition_cmd_core(parser & p, decl_cmd_kind kind, cmd_meta const & meta) {
    declaration_info_scope scope(p, kind, meta.m_modifiers);
    buffer<name> lp_names;
    buffer<expr> fns, params;
    /* TODO(Leo): allow a different doc string for each function in a mutual definition. */
    optional<std::string> doc_string = meta.m_doc_string;
    environment env = p.env();
    private_name_scope prv_scope(meta.m_modifiers.m_is_private, env);
    p.set_env(env);
    buffer<name> prv_names;
    auto header_pos = p.pos();
    expr val = parse_mutual_definition(p, lp_names, fns, prv_names, params);
    return elab_defs(p, kind, meta, lp_names, fns, prv_names, params, val, header_pos);
}

/* Return tuple (fn, val, actual_name) where

   - fn is a local constant with the user name + type
   - val is the actual definition
   - actual_name for the kernel declaration.
     Note that mlocal_pp_name_p(fn) and actual_name are different for scoped/private declarations.
*/
static std::tuple<expr, expr, name> parse_definition(parser & p, buffer<name> & lp_names, buffer<expr> & params,
                                                     bool is_example, bool is_instance, bool is_meta, bool is_abbrev) {
    parser::local_scope scope1(p);
    auto header_pos = p.pos();
    time_task _("parsing", p.mk_message(header_pos, INFORMATION));
    declaration_name_scope scope2;
    expr fn = parse_single_header(p, scope2, lp_names, params, is_example, is_instance);
    expr val;
    if (p.curr_is_token(get_assign_tk())) {
        p.next();
        if (is_meta) {
            declaration_name_scope scope2("_main");
            fn = mk_local(local_name_p(fn), local_pp_name_p(fn), local_type_p(fn), mk_rec_info());
            p.add_local(fn);
            val = p.parse_expr();
            /* add fake equation */
            expr eqn = copy_pos(val, mk_equation(fn, val));
            buffer<expr> eqns;
            eqns.push_back(eqn);
            val = mk_equations(p, fn, scope2.get_name(), scope2.get_actual_name(), eqns, {}, header_pos);
        } else {
            val = p.parse_expr();
        }
    } else if (p.curr_is_token(get_bar_tk()) || p.curr_is_token(get_period_tk())) {
        if (is_abbrev)
            throw exception("invalid abbreviation, abbreviations should not be defined using pattern matching");
        declaration_name_scope scope2("_main");
        fn = mk_local(local_name_p(fn), local_pp_name_p(fn), local_type_p(fn), mk_rec_info());
        p.add_local(fn);
        buffer<expr> eqns;
        if (p.curr_is_token(get_period_tk())) {
            auto period_pos = p.pos();
            p.next();
            eqns.push_back(p.save_pos(mk_no_equation(), period_pos));
        } else {
            while (p.curr_is_token(get_bar_tk())) {
                eqns.push_back(parse_equation(p, fn));
            }
            check_valid_end_of_equations(p);
        }
        optional<expr> wf_tacs = parse_using_well_founded(p);
        val = mk_equations(p, fn, scope2.get_name(), scope2.get_actual_name(), eqns, wf_tacs, header_pos);
    } else {
        val = p.parser_error_or_expr({"invalid definition, '|' or ':=' expected", p.pos()});
    }
    collect_implicit_locals(p, lp_names, params, {local_type_p(fn), val});
    return std::make_tuple(fn, val, scope2.get_actual_name());
}

static void replace_params(buffer<expr> const & params, buffer<expr> const & new_params, expr & fn, expr & val) {
    expr fn_type = replace_locals_preserving_pos_info(local_type_p(fn), params, new_params);
    expr new_fn  = update_local_p(fn, fn_type);
    val          = replace_locals_preserving_pos_info(val, params, new_params);
    val          = replace_local_preserving_pos_info(val, fn, new_fn);
    fn           = new_fn;
}

static expr_pair elaborate_theorem(elaborator & elab, expr const & fn, expr val) {
    expr fn_type = elab.elaborate_type(local_type_p(fn));
    elab.ensure_no_unassigned_metavars(fn_type);
    expr new_fn  = update_local_p(fn, fn_type);
    val = replace_local_preserving_pos_info(val, fn, new_fn);
    return elab.elaborate_with_type(val, mk_as_is(fn_type));
}

static expr_pair elaborate_definition_core(elaborator & elab, decl_cmd_kind kind, expr const & fn, expr const & val) {
    // We elaborate `fn` and `val` separately if `fn` is a theorem or its return type
    // was specified explicitly
    if (kind == decl_cmd_kind::Theorem || !is_placeholder(local_type_p(fn))) {
        return elaborate_theorem(elab, fn, val);
    } else {
        return elab.elaborate_with_type(val, local_type_p(fn));
    }
}

static expr_pair elaborate_definition(parser & p, elaborator & elab, decl_cmd_kind kind, expr const & fn, expr const & val, pos_info const & pos) {
    time_task _("elaboration", p.mk_message(pos, INFORMATION), local_pp_name_p(fn));
    return elaborate_definition_core(elab, kind, fn, val);
}

static void finalize_theorem_type(elaborator & elab, buffer<expr> const & params, expr & type,
                                  buffer<name> & lp_names,
                                  elaborator::theorem_finalization_info & info) {
    type = elab.mk_pi(params, type);
    buffer<name> implicit_lp_names;
    std::tie(type, info) = elab.finalize_theorem_type(type, implicit_lp_names);
    lp_names.append(implicit_lp_names);
}

static void finalize_theorem_proof(elaborator & elab, buffer<expr> const & params, expr & val,
                                   elaborator::theorem_finalization_info const & info) {
    val  = elab.mk_lambda(params, val);
    val = elab.finalize_theorem_proof(val, info);
}

static expr inline_new_defs(environment const & old_env, environment const & new_env, name const & n, expr const & e) {
    return replace(e, [=] (expr const & e, unsigned) -> optional<expr> {
        if (is_sorry(e)) {
            return none_expr();
        } else if (is_constant(e) && !old_env.find(const_name(e))) {
            auto decl = new_env.get(const_name(e));
            if (decl.has_value()) {
                expr val  = instantiate_value_lparams(decl, const_levels(e));
                return some_expr(inline_new_defs(old_env, new_env, n, val));
            } else {
                throw exception(sstream() << "invalid theorem '" << n << "', theorems should not depend on axioms introduced using "
                                "tactics (solution: mark theorem as a definition)");
            }
        } else {
            return none_expr();
        }
    });
}

static expr elaborate_proof(
        environment const & decl_env, options const & opts,
        pos_info const & header_pos,
        list<expr> const & params_list,
        expr const & fn, expr const & val0, elaborator::theorem_finalization_info const & finfo,
        bool /* is_rfl_lemma */, expr const & final_type,
        metavar_context const & mctx, local_context const & lctx,
        parser_pos_provider pos_provider, bool /* use_info_manager */, std::string const & file_name) {
    auto tc = std::make_shared<type_context_old>(decl_env, opts, mctx, lctx);
    scope_trace_env scope2(decl_env, opts, *tc);
    scope_traces_as_messages scope2a(file_name, header_pos);
    scope_pos_info_provider scope3(pos_provider);

    try {
        bool recover_from_errors = true;
        elaborator elab(decl_env, opts, get_namespace(decl_env) + local_pp_name_p(fn), mctx, lctx, recover_from_errors);

        expr val, type;
        {
            time_task _("elaboration", message_builder(tc, decl_env, get_global_ios(), file_name, header_pos, INFORMATION),
                        local_pp_name_p(fn));
            std::tie(val, type) = elab.elaborate_with_type(val0, mk_as_is(local_type_p(fn)));
        }

        if (is_equations_result(val))
            val = get_equations_result(val, 0);
        buffer<expr> params; for (auto & e : params_list) params.push_back(e);
        finalize_theorem_proof(elab, params, val, finfo);
        return inline_new_defs(decl_env, elab.env(), local_pp_name_p(fn), val);
    } catch (exception & ex) {
        /* Remark: we need the catch to be able to produce correct line information */
        message_builder(tc, decl_env, get_global_ios(), file_name, header_pos, ERROR)
            .set_exception(ex).report();
        return mk_sorry(*tc, final_type, true);
    }
}

static void check_example(environment const & decl_env, options const & opts,
                          decl_modifiers modifiers, bool /* noncomputable_theory */,
                          names const & univ_params, list<expr> const & params,
                          expr const & fn, expr const & val0,
                          metavar_context const & mctx, local_context const & lctx,
                          parser_pos_provider pos_provider, bool /* use_info_manager */, std::string const & file_name) {
    auto tc = std::make_shared<type_context_old>(decl_env, opts, mctx, lctx);
    scope_trace_env scope2(decl_env, opts, *tc);
    scope_traces_as_messages scope2a(file_name, pos_provider.get_some_pos());
    scope_pos_info_provider scope3(pos_provider);

    name decl_name = "_example";

    try {
        bool recover_from_errors = true;
        elaborator elab(decl_env, opts, decl_name, mctx, lctx, recover_from_errors);

        expr val, type;
        std::tie(val, type) = elab.elaborate_with_type(val0, local_type_p(fn));
        buffer<expr> params_buf; for (auto & p : params) params_buf.push_back(p);
        buffer<name> univ_params_buf; to_buffer(univ_params, univ_params_buf);
        finalize_definition(elab, params_buf, type, val, univ_params_buf);

        bool is_meta      = modifiers.m_is_meta;
        auto new_env = elab.env();
        declaration def = mk_definition(new_env, decl_name, names(univ_params_buf), type, val, is_meta);
        new_env = module::add(new_env, def);
    } catch (throwable & ex) {
        message_builder error_msg(tc, decl_env, get_global_ios(),
                                  pos_provider.get_file_name(), pos_provider.get_some_pos(),
                                  ERROR);
        error_msg.set_exception(ex);
        error_msg.report();
        throw;
    }
}

static bool is_rfl_preexpr(expr const & e) {
    return is_constant(e, get_rfl_name());
}

static environment elab_single_def(parser & p, decl_cmd_kind const & kind, cmd_meta meta, buffer <name> & lp_names,
                            buffer <expr> const & params, expr fn, expr val, pos_info const & header_pos,
                            name const & prv_name) {
    bool recover_from_errors = true;
    elaborator elab(p.env(), p.get_options(), get_namespace(p.env()) + local_pp_name_p(fn), metavar_context(), local_context(), recover_from_errors);
    buffer<expr> new_params;
    elaborate_params(elab, params, new_params);
    replace_params(params, new_params, fn, val);
    bool is_instance  = (kind == decl_cmd_kind::Instance);
    bool is_abbrev    = (kind == decl_cmd_kind::Abbreviation);
    bool is_rfl = false;
    if (is_instance)
        meta.m_attrs.set_attribute(p.env(), "instance");
    if (is_abbrev) {
        meta.m_attrs.set_attribute(p.env(), "inline");
        meta.m_attrs.set_attribute(p.env(), "reducible");
    }

    auto process = [&](expr val) -> environment {
        expr type;
        optional<expr> opt_val;
        bool eqns = false;
        name c_name = local_name_p(fn);
        pair<environment, name> env_n;
        if (kind == decl_cmd_kind::Theorem) {
            is_rfl = is_rfl_preexpr(val);
            type = elab.elaborate_type(local_type_p(fn));
            elab.ensure_no_unassigned_metavars(type);
            expr new_fn = update_local_p(fn, type);
            val = replace_local_preserving_pos_info(val, fn, new_fn);
            elaborator::theorem_finalization_info thm_finfo;
            finalize_theorem_type(elab, new_params, type, lp_names, thm_finfo);
            auto decl_env = elab.env();
            auto opts = p.get_options();
            auto new_params_list = to_list(new_params);
            auto mctx = elab.mctx();
            auto lctx = elab.lctx();
            auto pos_provider = p.get_parser_pos_provider(header_pos);
            bool use_info_manager = false; // get_global_info_manager() != nullptr;
            std::string file_name = p.get_file_name();
            opt_val = elaborate_proof(decl_env, opts, header_pos, new_params_list,
                                      new_fn, val, thm_finfo, is_rfl, type,
                                      mctx, lctx, pos_provider, use_info_manager, file_name);
            env_n = declare_definition(p, elab.env(), kind, lp_names, c_name, prv_name, type, opt_val, meta, is_abbrev, header_pos);
        } else if (kind == decl_cmd_kind::Example) {
            auto env = p.env();
            auto opts = p.get_options();
            auto lp_name_list = names(lp_names);
            auto new_params_list = to_list(new_params);
            auto mctx = elab.mctx();
            auto lctx = elab.lctx();
            auto pos_provider = p.get_parser_pos_provider(p.cmd_pos());
            bool use_info_manager = false; // get_global_info_manager() != nullptr;
            bool noncomputable_theory = p.ignore_noncomputable();
            std::string file_name = p.get_file_name();
            check_example(env, opts, meta.m_modifiers, noncomputable_theory,
                          lp_name_list, new_params_list, fn, val, mctx, lctx,
                          pos_provider, use_info_manager, file_name);
            return p.env();
        } else {
            std::tie(val, type) = elaborate_definition(p, elab, kind, fn, val, header_pos);
            eqns = is_equations_result(val);
            if (eqns) {
                lean_assert(is_equations_result(val));
                lean_assert(get_equations_result_size(val) == 1);
                val = get_equations_result(val, 0);
            }
            finalize_definition(elab, new_params, type, val, lp_names);
            env_n = declare_definition(p, elab.env(), kind, lp_names, c_name, prv_name, type, some_expr(val), meta, is_abbrev, header_pos);
        }
        time_task _("decl post-processing", p.mk_message(header_pos, INFORMATION), c_name);
        environment new_env = env_n.first;
        name c_real_name    = env_n.second;
        new_env = add_local_ref(p, new_env, c_name, c_real_name, lp_names, params);
        if (!meta.m_modifiers.m_is_meta && (kind == decl_cmd_kind::Definition || kind == decl_cmd_kind::Instance)) {
            new_env = mk_smart_unfolding_definition(new_env, p.get_options(), c_real_name);
        }
        /* Apply attributes last so that they may access any information on the new decl */
        return meta.m_attrs.apply(new_env, p.ios(), c_real_name);
    };

    try {
        return process(val);
    } catch (throwable & ex) {
        // Even though we catch exceptions during elaboration, there can still be other exceptions,
        // e.g. when adding a declaration to the environment.

        // If we have already logged an error during elaboration, don't
        // bother showing the less helpful kernel exception
        if (!global_message_log()->has_errors())
            p.mk_message(header_pos, ERROR).set_exception(ex).report();
        // As a last resort, try replacing the definition body with `sorry`.
        // If that doesn't work either, just silently give up since we have
        // already logged at least one error.
        try {
            return process(p.mk_sorry(header_pos, true));
        } catch (...) {
            return p.env();
        }
    }
}

environment elab_defs(parser & p, decl_cmd_kind kind, cmd_meta const & meta, buffer <name> lp_names, buffer <expr> const & fns,
                      buffer <name> const & prv_names, buffer <expr> const & params, expr val, pos_info const & header_pos) {
    if (meta.m_modifiers.m_is_mutual)
        return elab_defs_core(p, kind, meta, lp_names, fns, prv_names,
                              params, val, header_pos);
    else
        return elab_single_def(p, kind, meta, lp_names, params, fns[0], val, header_pos, prv_names[0]);
}

environment single_definition_cmd_core(parser & p, decl_cmd_kind kind, cmd_meta meta) {
    buffer<name> lp_names;
    buffer<expr> params;
    expr fn, val;
    auto header_pos = p.pos();
    declaration_info_scope scope(p, kind, meta.m_modifiers);
    environment env   = p.env();
    private_name_scope prv_scope(meta.m_modifiers.m_is_private, env);
    p.set_env(env);
    bool is_example   = (kind == decl_cmd_kind::Example);
    bool is_instance  = (kind == decl_cmd_kind::Instance);
    bool is_abbrev    = (kind == decl_cmd_kind::Abbreviation);
    name prv_name;
    std::tie(fn, val, prv_name) = parse_definition(p, lp_names, params, is_example, is_instance, meta.m_modifiers.m_is_meta, is_abbrev);

    // skip elaboration of definitions during reparsing
    if (p.get_break_at_pos())
        return p.env();

    return elab_single_def(p, kind, meta, lp_names, params, fn, val, header_pos, prv_name);
}

environment definition_cmd_core(parser & p, decl_cmd_kind kind, cmd_meta const & meta) {
    if (meta.m_modifiers.m_is_mutual)
        return mutual_definition_cmd_core(p, kind, meta);
    else
        return single_definition_cmd_core(p, kind, meta);
}
}
