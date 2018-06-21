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
#include "kernel/old_type_checker.h"
#include "kernel/declaration.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/explicit.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/scoped_ext.h"
#include "library/noncomputable.h"
#include "library/module.h"
#include "library/aux_definition.h"
#include "library/documentation.h"
#include "library/scope_pos_info_provider.h"
#include "library/replace_visitor.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/equations.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/eqn_lemmas.h"
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
        expr fn_type = parse_inner_header(p, mlocal_pp_name(pre_fn)).first;
        declaration_name_scope scope2(mlocal_pp_name(pre_fn));
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
        expr fn      = mk_local(mlocal_name(pre_fn), mlocal_pp_name(pre_fn), fn_type, mk_rec_info());
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

static certified_declaration check(parser & p, environment const & env, name const & c_name, declaration const & d, pos_info const & pos) {
    try {
        time_task _("type checking", p.mk_message(pos, INFORMATION), p.get_options(), c_name);
        return ::lean::check(env, d);
    } catch (kernel_exception & ex) {
        unsigned i = get_pp_indent(p.get_options());
        auto pp_fn = ::lean::mk_pp_ctx(env, p.get_options(), metavar_context(), local_context());
        format msg = format("kernel failed to type check declaration '") + format(c_name) + format("' ") +
            format("this is usually due to a buggy tactic or a bug in the builtin elaborator");
        msg += line() + format("elaborated type:");
        msg += nest(i, line() + pp_fn(d.get_type()));
        if (d.is_definition()) {
            msg += line() + format("elaborated value:");
            msg += nest(i, line() + pp_fn(d.get_value()));
        }
        throw nested_exception(msg, std::current_exception());
    }
}

static bool check_noncomputable(bool ignore_noncomputable, environment const & env, name const & c_name, name const & c_real_name, bool is_noncomputable,
                                std::string const & file_name, pos_info const & pos) {
    if (ignore_noncomputable)
        return true;
    if (!is_noncomputable && is_marked_noncomputable(env, c_real_name)) {
        auto reason = get_noncomputable_reason(env, c_real_name);
        lean_assert(reason);
        report_message(message(file_name, pos, ERROR,
                               (sstream() << "definition '" << c_name << "' is noncomputable, it depends on '" << *reason << "'").str()));
        return false;
    }
    if (is_noncomputable && !is_marked_noncomputable(env, c_real_name)) {
        report_message(message(file_name, pos, WARNING,
                               (sstream() << "definition '" << c_name << "' was incorrectly marked as noncomputable").str()));
    }
    return true;
}

static environment compile_decl(parser & p, environment const & env,
                                name const & c_name, name const & c_real_name, pos_info const & pos) {
    try {
        time_task _("compilation", p.mk_message(message_severity::INFORMATION), p.get_options(), c_real_name);
        return vm_compile(env, env.get(c_real_name));
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
    if (val && !meta.m_modifiers.m_is_meta && !old_type_checker(env).is_prop(type)) {
        /* We only abstract nested proofs if the type of the definition is not a proposition */
        std::tie(new_env, type) = abstract_nested_proofs(new_env, c_real_name, type);
        std::tie(new_env, *val) = abstract_nested_proofs(new_env, c_real_name, *val);
    }
    bool use_conv_opt = true;
    bool is_meta      = meta.m_modifiers.m_is_meta;
    auto def          =
        (kind == decl_cmd_kind::Theorem ?
         mk_theorem(c_real_name, names(lp_names), type, *val) :
         (is_abbrev ? mk_definition(c_real_name, names(lp_names), type, *val, reducibility_hints::mk_abbreviation(), is_meta) :
          mk_definition(new_env, c_real_name, names(lp_names), type, *val, use_conv_opt, is_meta)));
    auto cdef         = check(p, new_env, c_name, def, pos);
    new_env           = module::add(new_env, cdef);

    check_noncomputable(p.ignore_noncomputable(), new_env, c_name, c_real_name, meta.m_modifiers.m_is_noncomputable, p.get_file_name(), pos);

    if (meta.m_modifiers.m_is_protected)
        new_env = add_protected(new_env, c_real_name);

    new_env = add_alias(new_env, meta.m_modifiers.m_is_protected, c_name, c_real_name);

    if (!meta.m_modifiers.m_is_private) {
        new_env = ensure_decl_namespaces(new_env, c_real_name);
    }

    new_env = compile_decl(p, new_env, c_name, c_real_name, pos);
    if (meta.m_doc_string) {
        new_env = add_doc_string(new_env, c_real_name, *meta.m_doc_string);
    }
    return mk_pair(new_env, c_real_name);
}

static void throw_unexpected_error_at_copy_lemmas() {
    throw exception("unexpected error, failed to generate equational lemmas in the front-end");
}

/* Given e of the form Pi (a_1 : A_1) ... (a_n : A_n), lhs = rhs,
   return the pair (lhs, n) */
static pair<expr, unsigned> get_lemma_lhs(expr e) {
    unsigned nparams = 0;
    while (is_pi(e)) {
        nparams++;
        e = binding_body(e);
    }
    expr lhs, rhs;
    if (!is_eq(e, lhs, rhs))
        throw_unexpected_error_at_copy_lemmas();
    return mk_pair(lhs, nparams);
}

/*
   Given a lemma with parameters lp_names:
      [lp_1 ... lp_n]
   and the levels in the function application on the lemma left-hand-side lhs_fn_levels:
      [u_1 ... u_n] s.t. there is a permutation p s.t. p([u_1 ... u_n] = [(mk_univ_param lp_1) ... (mk_univ_param lp_n)],
   and levels fn_levels
      [v_1 ... v_n]
   Then, store
      p([v_1 ... v_n])
   in result.
*/
static void get_levels_for_instantiating_lemma(level_param_names const & lp_names,
                                               levels const & lhs_fn_levels,
                                               levels const & fn_levels,
                                               buffer<level> & result) {
    buffer<level> fn_levels_buffer;
    buffer<level> lhs_fn_levels_buffer;
    to_buffer(fn_levels, fn_levels_buffer);
    to_buffer(lhs_fn_levels, lhs_fn_levels_buffer);
    lean_assert(fn_levels_buffer.size() == lhs_fn_levels_buffer.size());
    for (name const & lp_name : lp_names) {
        unsigned j = 0;
        for (; j < lhs_fn_levels_buffer.size(); j++) {
            if (!is_param(lhs_fn_levels_buffer[j])) throw_unexpected_error_at_copy_lemmas();
            if (param_id(lhs_fn_levels_buffer[j]) == lp_name) {
                result.push_back(fn_levels_buffer[j]);
                break;
            }
        }
        lean_assert(j < lhs_fn_levels_buffer.size());
    }
}

/**
   Given a lemma with the given arity (i.e., number of nested Pi-terms),
   n = args.size() <= lhs_args.size(), and the first n
   arguments in lhs_args.size() are a permutation p of
     (var #0) ... (var #n-1)
   Then, store in result p(args)
*/
static void get_args_for_instantiating_lemma(unsigned arity,
                                             buffer<expr> const & lhs_args,
                                             buffer<expr> const & args,
                                             buffer<expr> & result) {
    for (unsigned i = 0; i < args.size(); i++) {
        if (!is_bvar(lhs_args[i]) || bvar_idx(lhs_args[i]) >= arity)
            throw_unexpected_error_at_copy_lemmas();
        result.push_back(args[arity - bvar_idx(lhs_args[i]).get_small_value() - 1]);
    }
}

/**
   Given declarations d_1, ..., d_n defined as
     (fun (a_1 : A_1) ... (a_n : A_n), d_1._main a_1' ... a_n')
   where a_1' ... a_n' is a permutation of a subset of a_1 ... a_n.
   Moreover, the parameters A_1 ... A_n are the same in all d_i's.
   Then, copy the equation lemmas from d._main to d.
*/
static environment copy_equation_lemmas(environment const & env, buffer<name> const & d_names) {
    type_context_old ctx(env, transparency_mode::All);
    type_context_old::tmp_locals locals(ctx);
    level_param_names lps;
    levels ls;
    buffer<expr> vals;
    buffer<expr> new_vals;
    for (unsigned d_idx = 0; d_idx < d_names.size(); d_idx++) {
        declaration const & d = env.get(d_names[d_idx]);
        expr val;
        if (d_idx == 0) {
            lps = d.get_univ_params();
            ls  = param_names_to_levels(lps);
            val = instantiate_value_univ_params(d, ls);
            while (is_lambda(val)) {
                expr local = locals.push_local_from_binding(val);
                val = instantiate(binding_body(val), local);
            }
        } else {
            val   = instantiate_value_univ_params(d, ls);
            for (expr const & local : locals.as_buffer()) {
                lean_assert(is_lambda(val));
                lean_assert(ctx.is_def_eq(ctx.infer(local), binding_domain(val)));
                val = instantiate(binding_body(val), local);
            }
        }
        buffer<expr> args;
        expr const & fn = get_app_args(val, args);
        if (!is_constant(fn) ||
            !std::all_of(args.begin(), args.end(), is_local)) {
            throw_unexpected_error_at_copy_lemmas();
        }
        vals.push_back(val);
        /* We want to create new equations where we replace val with new_val in the equations
           associated with fn. */
        expr new_val = mk_app(mk_constant(d_names[d_idx], ls), locals.as_buffer());
        new_vals.push_back(new_val);
    }
    /* Copy equations */
    environment new_env = env;
    for (unsigned d_idx = 0; d_idx < d_names.size(); d_idx++) {
        buffer<expr> args;
        expr const & fn = get_app_args(vals[d_idx], args);
        unsigned i = 1;
        while (true) {
            name eqn_name = mk_equation_name(const_name(fn), i);
            optional<declaration> eqn_decl = env.find(eqn_name);
            if (!eqn_decl) break;
            expr lhs; unsigned num_eqn_params;
            std::tie(lhs, num_eqn_params) = get_lemma_lhs(eqn_decl->get_type());
            buffer<expr> lhs_args;
            expr const & lhs_fn = get_app_args(lhs, lhs_args);
            if (!is_constant(lhs_fn) || const_name(lhs_fn) != const_name(fn) || lhs_args.size() < args.size())
                throw_unexpected_error_at_copy_lemmas();
            /* Get levels for instantiating the lemma */
            buffer<level> eqn_level_buffer;
            get_levels_for_instantiating_lemma(eqn_decl->get_univ_params(),
                                               const_levels(lhs_fn),
                                               const_levels(fn),
                                               eqn_level_buffer);
            levels eqn_levels(eqn_level_buffer);
            /* Get arguments for instantiating the lemma */
            buffer<expr> eqn_args;
            get_args_for_instantiating_lemma(num_eqn_params, lhs_args, args, eqn_args);
            /* Convert type */
            expr eqn_type = instantiate_type_univ_params(*eqn_decl, eqn_levels);
            for (unsigned j = 0; j < eqn_args.size(); j++) eqn_type = binding_body(eqn_type);
            eqn_type = instantiate_rev(eqn_type, eqn_args);
            expr new_eqn_type = replace(eqn_type, [&](expr const & e, unsigned) {
                    for (unsigned i = 0; i < vals.size(); i++) {
                        if (e == vals[i])
                            return some_expr(new_vals[i]);
                    }
                    return none_expr();
                });
            new_eqn_type = locals.mk_pi(new_eqn_type);
            name new_eqn_name    = mk_equation_name(d_names[d_idx], i);
            expr new_eqn_value;
            new_eqn_value = mk_app(mk_constant(eqn_name, eqn_levels), args);
            new_eqn_value = locals.mk_lambda(new_eqn_value);
            declaration new_decl = mk_theorem(new_eqn_name, lps, new_eqn_type, new_eqn_value);
            new_env = module::add(new_env, check(new_env, new_decl));
            if (is_rfl_lemma(env, eqn_name))
                new_env = mark_rfl_lemma(new_env, new_eqn_name);
            new_env = add_eqn_lemma(new_env, new_eqn_name);
            i++;
        }
    }
    return new_env;
}

/**
   Given a declaration d defined as
     (fun (a_1 : A_1) ... (a_n : A_n), d._main a_1' ... a_n')
   where a_1' ... a_n' is a permutation of a subset of a_1 ... a_n.
   Then, copy the equation lemmas from d._main to d.
*/
static environment copy_equation_lemmas(environment const & env, name const & d_name) {
    buffer<name> d_names;
    d_names.push_back(d_name);
    return copy_equation_lemmas(env, d_names);
}

static environment mutual_definition_cmd_core(parser & p, decl_cmd_kind kind, cmd_meta const & meta) {
    buffer<name> lp_names;
    buffer<expr> fns, params;
    declaration_info_scope scope(p, kind, meta.m_modifiers);
    auto header_pos = p.pos();
    /* TODO(Leo): allow a different doc string for each function in a mutual definition. */
    optional<std::string> doc_string = meta.m_doc_string;
    environment env = p.env();
    private_name_scope prv_scope(meta.m_modifiers.m_is_private, env);
    buffer<name> prv_names;
    expr val = parse_mutual_definition(p, lp_names, fns, prv_names, params);

    // skip elaboration of definitions during reparsing
    if (p.get_break_at_pos())
        return p.env();

    bool recover_from_errors = true;
    elaborator elab(env, p.get_options(), get_namespace(env) + mlocal_pp_name(fns[0]), metavar_context(), local_context(), recover_from_errors);
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
        name c_name = mlocal_name(fns[i]);
        name c_real_name;
        bool is_abbrev = false;
        std::tie(env, c_real_name) = declare_definition(p, env, kind, lp_names, c_name, prv_names[i],
                                                        curr_type, some_expr(curr), meta, is_abbrev, header_pos);
        env = add_local_ref(p, env, c_name, c_real_name, lp_names, params);
        new_d_names.push_back(c_real_name);
        elab.set_env(env);
    }
    /* Add lemmas */
    elab.set_env(copy_equation_lemmas(elab.env(), new_d_names));
    /* Apply attributes last so that they may access any information on the new decl */
    for (auto const & c_real_name : new_d_names) {
        elab.set_env(meta.m_attrs.apply(elab.env(), p.ios(), c_real_name));
    }
    return elab.env();
}

/* Return tuple (fn, val, actual_name) where

   - fn is a local constant with the user name + type
   - val is the actual definition
   - actual_name for the kernel declaration.
     Note that mlocal_pp_name(fn) and actual_name are different for scoped/private declarations.
*/
static std::tuple<expr, expr, name> parse_definition(parser & p, buffer<name> & lp_names, buffer<expr> & params,
                                                     bool is_example, bool is_instance, bool is_meta, bool is_abbrev) {
    parser::local_scope scope1(p);
    auto header_pos = p.pos();
    time_task _("parsing", p.mk_message(header_pos, INFORMATION), p.get_options());
    declaration_name_scope scope2;
    expr fn = parse_single_header(p, scope2, lp_names, params, is_example, is_instance);
    expr val;
    if (p.curr_is_token(get_assign_tk())) {
        p.next();
        if (is_meta) {
            declaration_name_scope scope2("_main");
            fn = mk_local(mlocal_name(fn), mlocal_pp_name(fn), mlocal_type(fn), mk_rec_info());
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
        fn = mk_local(mlocal_name(fn), mlocal_pp_name(fn), mlocal_type(fn), mk_rec_info());
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
    collect_implicit_locals(p, lp_names, params, {mlocal_type(fn), val});
    return std::make_tuple(fn, val, scope2.get_actual_name());
}

static void replace_params(buffer<expr> const & params, buffer<expr> const & new_params, expr & fn, expr & val) {
    expr fn_type = replace_locals_preserving_pos_info(mlocal_type(fn), params, new_params);
    expr new_fn  = update_mlocal(fn, fn_type);
    val          = replace_locals_preserving_pos_info(val, params, new_params);
    val          = replace_local_preserving_pos_info(val, fn, new_fn);
    fn           = new_fn;
}

static expr_pair elaborate_theorem(elaborator & elab, expr const & fn, expr val) {
    expr fn_type = elab.elaborate_type(mlocal_type(fn));
    elab.ensure_no_unassigned_metavars(fn_type);
    expr new_fn  = update_mlocal(fn, fn_type);
    val = replace_local_preserving_pos_info(val, fn, new_fn);
    return elab.elaborate_with_type(val, mk_as_is(fn_type));
}

static expr_pair elaborate_definition_core(elaborator & elab, decl_cmd_kind kind, expr const & fn, expr const & val) {
    // We elaborate `fn` and `val` separately if `fn` is a theorem or its return type
    // was specified explicitly
    if (kind == decl_cmd_kind::Theorem || !is_placeholder(mlocal_type(fn))) {
        return elaborate_theorem(elab, fn, val);
    } else {
        return elab.elaborate_with_type(val, mlocal_type(fn));
    }
}

static expr_pair elaborate_definition(parser & p, elaborator & elab, decl_cmd_kind kind, expr const & fn, expr const & val, pos_info const & pos) {
    time_task _("elaboration", p.mk_message(pos, INFORMATION), p.get_options(), mlocal_pp_name(fn));
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
            if (decl.is_definition()) {
                expr val  = instantiate_value_univ_params(decl, const_levels(e));
                lean_assert(decl.is_definition());
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
        bool is_rfl_lemma, expr const & final_type,
        metavar_context const & mctx, local_context const & lctx,
        parser_pos_provider pos_provider, bool use_info_manager, std::string const & file_name) {
    auto tc = std::make_shared<type_context_old>(decl_env, opts, mctx, lctx);
    scope_trace_env scope2(decl_env, opts, *tc);
    scope_traces_as_messages scope2a(file_name, header_pos);
    scope_pos_info_provider scope3(pos_provider);
    auto_reporting_info_manager_scope scope4(file_name, use_info_manager);

    try {
        bool recover_from_errors = true;
        elaborator elab(decl_env, opts, get_namespace(decl_env) + mlocal_pp_name(fn), mctx, lctx, recover_from_errors);

        expr val, type;
        {
            time_task _("elaboration", message_builder(tc, decl_env, get_global_ios(), file_name, header_pos, INFORMATION),
                        opts, mlocal_pp_name(fn));
            std::tie(val, type) = elab.elaborate_with_type(val0, mk_as_is(mlocal_type(fn)));
        }

        if (is_equations_result(val))
            val = get_equations_result(val, 0);
        buffer<expr> params; for (auto & e : params_list) params.push_back(e);
        finalize_theorem_proof(elab, params, val, finfo);
        if (is_rfl_lemma && !lean::is_rfl_lemma(final_type, val))
            throw exception("not a rfl-lemma, even though marked as rfl");
        return inline_new_defs(decl_env, elab.env(), mlocal_pp_name(fn), val);
    } catch (exception & ex) {
        /* Remark: we need the catch to be able to produce correct line information */
        message_builder(tc, decl_env, get_global_ios(), file_name, header_pos, ERROR)
            .set_exception(ex).report();
        return mk_sorry(*tc, final_type, true);
    }
}

static void check_example(environment const & decl_env, options const & opts,
                          decl_modifiers modifiers, bool noncomputable_theory,
                          level_param_names const & univ_params, list<expr> const & params,
                          expr const & fn, expr const & val0,
                          metavar_context const & mctx, local_context const & lctx,
                          parser_pos_provider pos_provider, bool use_info_manager, std::string const & file_name) {
    auto tc = std::make_shared<type_context_old>(decl_env, opts, mctx, lctx);
    scope_trace_env scope2(decl_env, opts, *tc);
    scope_traces_as_messages scope2a(file_name, pos_provider.get_some_pos());
    scope_pos_info_provider scope3(pos_provider);
    auto_reporting_info_manager_scope scope4(file_name, use_info_manager);
    module::scope_pos_info scope_pos(pos_provider.get_some_pos());

    name decl_name = "_example";

    try {
        bool recover_from_errors = true;
        elaborator elab(decl_env, opts, decl_name, mctx, lctx, recover_from_errors);

        expr val, type;
        std::tie(val, type) = elab.elaborate_with_type(val0, mlocal_type(fn));
        buffer<expr> params_buf; for (auto & p : params) params_buf.push_back(p);
        buffer<name> univ_params_buf; to_buffer(univ_params, univ_params_buf);
        finalize_definition(elab, params_buf, type, val, univ_params_buf);

        bool use_conv_opt = true;
        bool is_meta      = modifiers.m_is_meta;
        auto new_env = elab.env();
        auto def = mk_definition(new_env, decl_name, names(univ_params_buf), type, val, use_conv_opt, is_meta);
        auto cdef = check(new_env, def);
        new_env = module::add(new_env, cdef);
        check_noncomputable(noncomputable_theory, new_env, decl_name, def.get_name(), modifiers.m_is_noncomputable,
                                 pos_provider.get_file_name(), pos_provider.get_some_pos());
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

environment single_definition_cmd_core(parser & p, decl_cmd_kind kind, cmd_meta meta) {
    buffer<name> lp_names;
    buffer<expr> params;
    expr fn, val;
    auto header_pos = p.pos();
    module::scope_pos_info scope_pos(header_pos);
    declaration_info_scope scope(p, kind, meta.m_modifiers);
    environment env   = p.env();
    private_name_scope prv_scope(meta.m_modifiers.m_is_private, env);
    bool is_example   = (kind == decl_cmd_kind::Example);
    bool is_instance  = (kind == decl_cmd_kind::Instance);
    bool is_abbrev    = (kind == decl_cmd_kind::Abbreviation);
    bool aux_lemmas   = scope.gen_aux_lemmas();
    bool is_rfl       = false;
    if (is_instance)
        meta.m_attrs.set_attribute(env, "instance");
    if (is_abbrev) {
        meta.m_attrs.set_attribute(env, "inline");
        meta.m_attrs.set_attribute(env, "reducible");
    }
    name prv_name;
    std::tie(fn, val, prv_name) = parse_definition(p, lp_names, params, is_example, is_instance, meta.m_modifiers.m_is_meta, is_abbrev);

    auto begin_pos = p.cmd_pos();
    auto end_pos = p.pos();
    scope_log_tree lt(logtree().mk_child({}, (get_namespace(env) + mlocal_pp_name(fn)).to_string(),
                                         {logtree().get_location().m_file_name, {begin_pos, end_pos}}));

    // skip elaboration of definitions during reparsing
    if (p.get_break_at_pos())
        return p.env();

    bool recover_from_errors = true;
    elaborator elab(env, p.get_options(), get_namespace(env) + mlocal_pp_name(fn), metavar_context(), local_context(), recover_from_errors);
    buffer<expr> new_params;
    elaborate_params(elab, params, new_params);
    elab.freeze_local_instances();
    replace_params(params, new_params, fn, val);

    auto process = [&](expr val) -> environment {
        expr type;
        optional<expr> opt_val;
        bool eqns = false;
        name c_name = mlocal_name(fn);
        pair<environment, name> env_n;
        if (kind == decl_cmd_kind::Theorem) {
            is_rfl = is_rfl_preexpr(val);
            type = elab.elaborate_type(mlocal_type(fn));
            elab.ensure_no_unassigned_metavars(type);
            expr new_fn = update_mlocal(fn, type);
            val = replace_local_preserving_pos_info(val, fn, new_fn);
            elaborator::theorem_finalization_info thm_finfo;
            finalize_theorem_type(elab, new_params, type, lp_names, thm_finfo);
            auto decl_env = elab.env();
            auto opts = p.get_options();
            auto new_params_list = to_list(new_params);
            auto mctx = elab.mctx();
            auto lctx = elab.lctx();
            auto pos_provider = p.get_parser_pos_provider(header_pos);
            bool use_info_manager = get_global_info_manager() != nullptr;
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
            bool use_info_manager = get_global_info_manager() != nullptr;
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
        time_task _("decl post-processing", p.mk_message(header_pos, INFORMATION), p.get_options(), c_name);
        environment new_env = env_n.first;
        name c_real_name    = env_n.second;
        if (is_rfl) new_env = mark_rfl_lemma(new_env, c_real_name);
        new_env = add_local_ref(p, new_env, c_name, c_real_name, lp_names, params);
        if (eqns && aux_lemmas) {
            new_env = copy_equation_lemmas(new_env, c_real_name);
        }
        if (!meta.m_modifiers.m_is_meta && (kind == decl_cmd_kind::Definition || kind == decl_cmd_kind::Instance)) {
            if (!eqns) {
                unsigned arity = new_params.size();
                new_env = mk_simple_equation_lemma_for(new_env, p.get_options(), meta.m_modifiers.m_is_private, c_name, c_real_name, arity);
            } else {
                new_env = mk_smart_unfolding_definition(new_env, p.get_options(), c_real_name);
            }
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
        if (!lt.get().has_entry_now(is_error_message))
            p.mk_message(header_pos, ERROR).set_exception(ex).report();
        // As a last resort, try replacing the definition body with `sorry`.
        // If that doesn't work either, just silently give up since we have
        // already logged at least one error.
        try {
            return process(p.mk_sorry(header_pos, true));
        } catch (...) {
            return env;
        }
    }
}

environment definition_cmd_core(parser & p, decl_cmd_kind kind, cmd_meta const & meta) {
    if (meta.m_modifiers.m_is_mutual)
        return mutual_definition_cmd_core(p, kind, meta);
    else
        return single_definition_cmd_core(p, kind, meta);
}
}
