/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/find_fn.h"
#include "library/scope_pos_info_provider.h"
#include "library/util.h"
#include "library/module.h"
#include "library/aliases.h"
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/private.h"
#include "library/locals.h"
#include "library/idx_metavar.h"
#include "library/constants.h"
#include "library/annotation.h"
#include "library/num.h"
#include "library/string.h"
#include "library/replace_visitor.h"
#include "library/aux_definition.h"
#include "library/comp_val.h"
#include "library/compiler/compiler.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/wf_rec.h"

#ifndef LEAN_DEFAULT_EQN_COMPILER_LEMMAS
#define LEAN_DEFAULT_EQN_COMPILER_LEMMAS false
#endif

#ifndef LEAN_DEFAULT_EQN_COMPILER_ZETA
#define LEAN_DEFAULT_EQN_COMPILER_ZETA false
#endif

namespace lean {
static name * g_eqn_compiler_zeta   = nullptr;

bool get_eqn_compiler_zeta(options const & o) {
    return o.get_bool(*g_eqn_compiler_zeta, LEAN_DEFAULT_EQN_COMPILER_ZETA);
}


[[ noreturn ]] void throw_ill_formed_eqns() {
    throw exception("ill-formed match/equations expression");
}

static optional<pair<expr, unsigned>> get_eqn_fn_and_arity(expr e) {
    while (is_lambda(e))
        e = binding_body(e);
    if (!is_equation(e) && !is_no_equation(e)) throw_ill_formed_eqns();
    if (is_no_equation(e)) {
        return optional<pair<expr, unsigned>>();
    } else {
        expr const & lhs = equation_lhs(e);
        expr const & fn  = get_app_fn(lhs);
        lean_assert(is_local(fn));
        return optional<pair<expr, unsigned>>(fn, get_app_num_args(lhs));
    }
}

static expr consume_fn_prefix(expr eq, buffer<expr> const & fns) {
    for (unsigned i = 0; i < fns.size(); i++) {
        if (!is_lambda(eq)) throw_ill_formed_eqns();
        eq = binding_body(eq);
    }
    return instantiate_rev(eq, fns);
}

unpack_eqns::unpack_eqns(type_context_old & ctx, expr const & e):
    m_locals(ctx) {
    lean_assert(is_equations(e));
    m_src = e;
    buffer<expr> eqs;
    unsigned num_fns = equations_num_fns(e);
    to_equations(e, eqs);
    /* Extract functions. */
    if (eqs.size() == 0) throw_ill_formed_eqns();
    expr eq = eqs[0];
    for (unsigned i = 0; i < num_fns; i++) {
        if (!is_lambda(eq)) throw_ill_formed_eqns();
        if (has_loose_bvars(binding_domain(eq))) throw_ill_formed_eqns();
        m_fns.push_back(m_locals.push_local(binding_name(eq), binding_domain(eq)));
        eq = binding_body(eq);
    }
    /* Extract equations */
    unsigned eqidx = 0;
    for (unsigned fidx = 0; fidx < num_fns; fidx++) {
        m_eqs.push_back(buffer<expr>());
        buffer<expr> & fn_eqs = m_eqs.back();
        if (eqidx >= eqs.size()) throw_ill_formed_eqns();
        expr eq = consume_fn_prefix(eqs[eqidx], m_fns);
        fn_eqs.push_back(eq);
        eqidx++;
        if (auto p = get_eqn_fn_and_arity(eq)) {
            if (p->first != m_fns[fidx]) throw_ill_formed_eqns();
            unsigned arity = p->second;
            m_arity.push_back(arity);
            while (eqidx < eqs.size()) {
                expr eq = consume_fn_prefix(eqs[eqidx], m_fns);
                if (auto p = get_eqn_fn_and_arity(eq)) {
                    if (p->first == m_fns[fidx]) {
                        if (p->second != arity) throw_ill_formed_eqns();
                        fn_eqs.push_back(eq);
                        eqidx++;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        } else {
            /* noequation, guess arity using type of function */
            type_context_old::tmp_locals locals(ctx);
            expr type = ctx.relaxed_whnf(ctx.infer(m_fns[fidx]));
            unsigned arity = 0;
            while (is_pi(type)) {
                arity++;
                type = ctx.relaxed_whnf(instantiate(binding_body(type),
                                                    locals.push_local_from_binding(type)));
            }
            if (arity == 0) throw_ill_formed_eqns();
            m_arity.push_back(arity);
        }
    }
    if (eqs.size() != eqidx) throw_ill_formed_eqns();
    lean_assert(m_arity.size() == m_fns.size());
    lean_assert(m_eqs.size() == m_fns.size());
}

expr unpack_eqns::update_fn_type(unsigned fidx, expr const & type) {
    expr new_fn = m_locals.push_local(local_pp_name(m_fns[fidx]), type, mk_rec_info());
    m_fns[fidx] = new_fn;
    return new_fn;
}

expr unpack_eqns::repack() {
    buffer<expr> new_eqs;
    for (buffer<expr> const & fn_eqs : m_eqs) {
        for (expr const & eq : fn_eqs) {
            new_eqs.push_back(m_locals.ctx().mk_lambda(m_fns, unwrap_pos(eq)));
        }
    }
    return update_equations(m_src, new_eqs);
}

unpack_eqn::unpack_eqn(type_context_old & ctx, expr const & eqn):
    m_src(eqn), m_locals(ctx) {
    expr it = eqn;
    while (is_lambda(it)) {
        expr d = instantiate_rev(binding_domain(it), m_locals.as_buffer().size(), m_locals.as_buffer().data());
        m_vars.push_back(m_locals.push_local(binding_name(it), d, binding_info(it)));
        it = binding_body(it);
    }
    it = instantiate_rev(it, m_locals.as_buffer().size(), m_locals.as_buffer().data());
    if (!is_equation(it)) throw_ill_formed_eqns();
    m_nested_src = it;
    m_lhs = equation_lhs(it);
    m_rhs = equation_rhs(it);
    m_ignore_if_unused = ignore_equation_if_unused(it);
}

expr unpack_eqn::add_var(name const & n, expr const & type) {
    m_modified_vars = true;
    m_vars.push_back(m_locals.push_local(n, type));
    return m_vars.back();
}

expr unpack_eqn::repack() {
    if (!m_modified_vars &&
        equation_lhs(m_nested_src) == m_lhs &&
        equation_rhs(m_nested_src) == m_rhs) return m_src;
    expr new_eq = copy_pos(m_nested_src, mk_equation(m_lhs, m_rhs, m_ignore_if_unused));
    return copy_pos(m_src, m_locals.ctx().mk_lambda(m_vars, new_eq));
}

bool is_recursive_eqns(type_context_old & ctx, expr const & e) {
    unpack_eqns ues(ctx, e);
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        buffer<expr> const & eqns = ues.get_eqns_of(fidx);
        for (expr const & eqn : eqns) {
            expr it = eqn;
            while (is_lambda(it)) {
                it = binding_body(it);
            }
            if (!is_equation(it) && !is_no_equation(it)) throw_ill_formed_eqns();
            if (is_equation(it)) {
                expr const & rhs = equation_rhs(it);
                if (find(rhs, [&](expr const & e, unsigned) {
                            if (is_local(e)) {
                                for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
                                    if (local_name(e) == local_name(ues.get_fn(fidx)))
                                        return true;
                                }
                            }
                            return false;
                        })) {
                    return true;
                }
            }
        }
    }
    return false;
}

bool has_inaccessible_annotation(expr const & e) {
    return static_cast<bool>(find(e, [&](expr const & e, unsigned) { return is_inaccessible(e); }));
}

class erase_inaccessible_annotations_fn : public replace_visitor {
    virtual expr visit_mdata(expr const & e) override {
        if (is_inaccessible(e)) {
            return visit(get_annotation_arg(e));
        } else {
            return replace_visitor::visit_mdata(e);
        }
    }
};

expr erase_inaccessible_annotations(expr const & e) {
    if (has_inaccessible_annotation(e))
        return erase_inaccessible_annotations_fn()(e);
    else
        return e;
}

list<expr> erase_inaccessible_annotations(list<expr> const & es) {
    return map(es, [&](expr const & e) { return erase_inaccessible_annotations(e); });
}

local_context erase_inaccessible_annotations(local_context const & lctx) {
    local_context r;
    r.m_next_idx        = lctx.m_next_idx;
    lctx.m_idx2local_decl.for_each([&](unsigned, local_decl const & d) {
            expr new_type = erase_inaccessible_annotations(d.get_type());
            optional<expr> new_value;
            if (auto val = d.get_value())
                new_value = erase_inaccessible_annotations(*val);
            auto new_d = local_context::update_local_decl(d, new_type, new_value);
            r.m_name2local_decl.insert(d.get_name(), new_d);
            r.m_idx2local_decl.insert(d.get_idx(), new_d);
            r.insert_user_name(d);
        });
    return r;
}

static void throw_mk_aux_definition_error(local_context const & lctx, name const & c, expr const & type, expr const & value, std::exception_ptr const & ex) {
    sstream strm;
    strm << "equation compiler failed to create auxiliary declaration '" << c << "'";
    if (contains_let_local_decl(lctx, type) || contains_let_local_decl(lctx, value)) {
        strm << ", auxiliary declaration has references to let-declarations (possible solution: use 'set_option eqn_compiler.zeta true')";
    }
    throw nested_exception(strm, ex);
}

void compile_aux_definition(environment & env, options const & opts, equations_header const & header, name const & user_name, name const & actual_name) {
    if (header.m_gen_code) {
        try {
            env = compile(env, opts, actual_name);
        } catch (exception & ex) {
            if (!header.m_prev_errors) {
                throw nested_exception(sstream() << "equation compiler failed to generate bytecode for "
                                       << "auxiliary declaration '" << user_name << "'", std::current_exception());
            }
        }
    }
}

pair<environment, expr> mk_aux_definition(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx,
                                          equations_header const & header, name const & c, name const & actual_c, expr const & type, expr const & value) {
    lean_trace("eqn_compiler", tout() << "declaring auxiliary definition\n" << c << " : " << type << "\n";);
    environment new_env = env;
    expr new_type       = type;
    expr new_value      = value;
    bool zeta           = get_eqn_compiler_zeta(opts);
    if (zeta) {
        new_type  = zeta_expand(lctx, new_type);
        new_value = zeta_expand(lctx, new_value);
    }
    name new_c          = actual_c;
    if (header.m_is_private) {
        new_env = register_private_name(env, c, actual_c);
        new_env = add_expr_alias(new_env, c, actual_c);
    }
    expr r;
    try {
        std::tie(new_env, r) = header.m_is_lemma ?
            mk_aux_lemma(new_env, mctx, lctx, new_c, new_type, new_value) :
            mk_aux_definition(new_env, mctx, lctx, new_c, new_type, new_value);
    } catch (exception & ex) {
        throw_mk_aux_definition_error(lctx, c, new_type, new_value, std::current_exception());
    }
    compile_aux_definition(new_env, opts, header, c, new_c);
    return mk_pair(new_env, r);
}

bool is_name_value(expr const & e) {
    if (is_constant(e, get_lean_name_anonymous_name()))
        return true;
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_constant(fn, get_lean_name_mk_string_name()) && args.size() == 2)
        return is_name_value(args[0]) && is_string_value(args[1]);
    if (is_constant(fn, get_lean_name_mk_numeral_name()) && args.size() == 2)
        return is_name_value(args[0]) && is_num(args[1]);
    return false;
}

bool is_nat_int_char_string_name_value(type_context_old & ctx, expr const & e) {
    if (is_char_value(ctx, e) || is_string_value(e) || is_name_value(e)) return true;
    if (is_signed_num(e)) {
        expr type = ctx.infer(e);
        if (ctx.is_def_eq(type, mk_nat_type()) || ctx.is_def_eq(type, mk_int_type()))
            return true;
    }
    return false;
}

static bool is_inductive(environment const & env, expr const & e) {
    return is_constant(e) && is_inductive(env, const_name(e));
}

/* Normalize until head is an inductive datatype */
static expr whnf_inductive(type_context_old & ctx, expr const & e) {
    return ctx.whnf_head_pred(e, [&](expr const & e) {
            return !is_inductive(ctx.env(), get_app_fn(e));
        });
}

/* Given a variable (x : I A idx), where (I A idx) is an inductive datatype,
   for each constructor c of (I A idx), this function invokes fn(t, new_vars) where t is of the form (c A ...),
   where new_vars are fresh variables and are arguments of (c A ...)
   which have not been fixed by typing constraints. Moreover, fn is only invoked if
   the type of (c A ...) matches (I A idx). */
void for_each_compatible_constructor(type_context_old & ctx, expr const & var,
                                     std::function<void(expr const &, buffer<expr> &)> const & fn) {
    lean_assert(is_local(var));
    expr var_type = whnf_inductive(ctx, ctx.infer(var));
    buffer<expr> I_args;
    expr const & I       = get_app_args(var_type, I_args);
    name const & I_name  = const_name(I);
    levels const & I_ls  = const_levels(I);
    constant_info I_info = ctx.env().get(I_name);
    lean_assert(I_info.is_inductive());
    inductive_val I_val  = I_info.to_inductive_val();
    unsigned nparams     = I_val.get_nparams();
    buffer<expr> I_params;
    I_params.append(nparams, I_args.data());
    buffer<name> constructor_names;
    get_constructor_names(ctx.env(), I_name, constructor_names);
    for (name const & c_name : constructor_names) {
        buffer<expr> c_vars;
        buffer<name> c_var_names;
        buffer<expr> new_c_vars;
        expr c  = mk_app(mk_constant(c_name, I_ls), I_params);
        expr it = whnf_inductive(ctx, ctx.infer(c));
        {
            type_context_old::tmp_mode_scope scope(ctx);
            while (is_pi(it)) {
                expr new_arg = ctx.mk_tmp_mvar(binding_domain(it));
                c_vars.push_back(new_arg);
                c_var_names.push_back(binding_name(it));
                c  = mk_app(c, new_arg);
                it = whnf_inductive(ctx, instantiate(binding_body(it), new_arg));
            }
            if (!ctx.is_def_eq(var_type, it)) {
                /* TODO(Leo): do we need this trace?
                trace_match(
                    auto pp = mk_pp_ctx(ctx.lctx());
                    tout() << "constructor '" << c_name << "' not being considered at complete transition because type\n" << pp(it)
                    << "\ndoes not match\n" << pp(var_type) << "\n";);
                */
                continue;
            }
            lean_assert(c_vars.size() == c_var_names.size());
            for (unsigned i = 0; i < c_vars.size(); i++) {
                expr & c_var = c_vars[i];
                c_var = ctx.instantiate_mvars(c_var);
                if (is_idx_metavar(c_var)) {
                    expr new_c_var = ctx.push_local(c_var_names[i], ctx.instantiate_mvars(ctx.infer(c_var)));
                    new_c_vars.push_back(new_c_var);
                    ctx.assign(c_var, new_c_var);
                    c_var = new_c_var;
                } else if (has_idx_metavar(c_var)) {
                    /* TODO(Leo): do we need this trace?
                    trace_match(
                        auto pp = mk_pp_ctx(ctx.lctx());
                        tout() << "constructor '" << c_name << "' not being considered because at complete transition because " <<
                        "failed to synthesize arguments\n" << pp(ctx.instantiate_mvars(c)) << "\n";);
                    */
                    continue;
                }
            }
            c = ctx.instantiate_mvars(c);
        }
        fn(c, new_c_vars);
    }
}

/* Given the telescope vars [x_1, ..., x_i, ..., x_n] and var := x_i,
   and t is a term containing variables t_vars := {y_1, ..., y_k} disjoint from {x_1, ..., x_n},
   Return [x_1, ..., x_{i-1}, y_1, ..., y_k, T(x_{i+1}), ..., T(x_n)},
   where T(x_j) updates the type of x_j (j > i) by replacing x_i with t.

   \remark The set of variables in t is a subset of {x_1, ..., x_{i-1}} union {y_1, ..., y_k}
*/
void update_telescope(type_context_old & ctx, buffer<expr> const & vars, expr const & var,
                      expr const & t, buffer<expr> const & t_vars, buffer<expr> & new_vars,
                      buffer<expr> & from, buffer<expr> & to) {
    /* We are replacing `var` with `c` */
    for (expr const & curr : vars) {
        if (curr == var) {
            from.push_back(var);
            to.push_back(t);
            new_vars.append(t_vars);
        } else {
            expr curr_type     = ctx.infer(curr);
            expr new_curr_type = replace_locals(curr_type, from, to);
            if (curr_type == new_curr_type) {
                new_vars.push_back(curr);
            } else {
                expr new_curr = ctx.push_local(local_pp_name(curr), new_curr_type);
                from.push_back(curr);
                to.push_back(new_curr);
                new_vars.push_back(new_curr);
            }
        }
    }
}

/* Helper functor for mk_smart_unfolding_definition */
struct replace_aux_meta_fn : public replace_visitor {
    name const & m_fn_aux_name;
    expr const & m_new_fn;
    unsigned     m_nargs_to_skip;
    bool         m_found{false};

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (is_constant(fn) && const_name(fn) == m_fn_aux_name) {
            if (args.size() >= m_nargs_to_skip) {
                m_found = true;
                for (unsigned i = m_nargs_to_skip; i < args.size(); i++) {
                    expr & arg   = args[i];
                    arg          = visit(arg);
                }
                return mk_app(m_new_fn, args.size() - m_nargs_to_skip, args.data() + m_nargs_to_skip);
            } else {
                throw exception("failed to generate helper declaration for smart unfolding, unexpected occurrence of recursive application");
            }
        } else {
            expr new_fn   = visit(fn);
            bool modified = !is_eqp(fn, new_fn);
            for (expr & arg : args) {
                expr new_arg = visit(arg);
                if (!is_eqp(new_arg, arg))
                    modified = true;
                arg = new_arg;
            }
            if (!modified)
                return e;
            else
                return mk_app(new_fn, args);
        }
    }

    replace_aux_meta_fn(name const & fn_aux_name, expr const & new_fn, unsigned nargs_to_skip):
        m_fn_aux_name(fn_aux_name),
        m_new_fn(new_fn),
        m_nargs_to_skip(nargs_to_skip) {
    }
};

environment mk_smart_unfolding_definition(environment const & env, options const & o, name const & n) {
    type_context_old ctx(env, o, metavar_context(), local_context());
    constant_info info = env.get(n);
    expr val  = info.get_value();
    levels ls = lparams_to_levels(info.get_lparams());
    type_context_old::tmp_locals locals(ctx);
    while (is_lambda(val)) {
        val = instantiate(binding_body(val), locals.push_local_from_binding(val));
    }
    expr const & fn      = get_app_fn(val);
    buffer<expr> args;
    get_app_rev_args(val, args);

    if (!is_constant(fn) || const_name(fn) != name(n, "_main")) {
        return env;
    }

    name const & fn_name = const_name(fn);

    if (uses_well_founded_recursion(env, fn_name)) {
        return env;
    }

    name meta_aux_fn_name = mk_meta_rec_name(fn_name);

    expr helper_value;
    if (optional<constant_info> aux_info = env.find(meta_aux_fn_name)) {
        expr new_fn  = mk_app(mk_constant(n, ls), locals.size(), locals.data());
        helper_value = instantiate_value_lparams(*aux_info, const_levels(fn));
        helper_value = apply_beta(helper_value, args.size(), args.data());
        replace_aux_meta_fn proc(meta_aux_fn_name, new_fn, args.size());
        helper_value = proc(helper_value);
        if (!proc.m_found)
            throw exception("failed to generate helper declaration for smart unfolding, auxiliary meta declaration does not contain recursive application");
    } else {
        helper_value = instantiate_value_lparams(env.get(fn_name), const_levels(fn));
        helper_value = apply_beta(helper_value, args.size(), args.data());
    }

    helper_value = locals.mk_lambda(helper_value);
    try {
        declaration def = mk_definition(env, mk_smart_unfolding_name_for(n), info.get_lparams(), info.get_type(), helper_value, true);
        return module::add(env, def);
    } catch (exception & ex) {
        throw nested_exception("failed to generate helper declaration for smart unfolding, type error", std::current_exception());
    }
}

void initialize_eqn_compiler_util() {
    register_trace_class("eqn_compiler");
    register_trace_class(name{"debug", "eqn_compiler"});

    g_eqn_compiler_zeta   = new name{"eqn_compiler", "zeta"};
    register_bool_option(*g_eqn_compiler_zeta, LEAN_DEFAULT_EQN_COMPILER_ZETA,
                         "(equation compiler) apply zeta-expansion (expand references to let-declarations) before creating auxiliary definitions.");
}

void finalize_eqn_compiler_util() {
    delete g_eqn_compiler_zeta;
}
}
