/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/find_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/user_recursors.h"
#include "library/aux_recursors.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/scope_pos_info_provider.h"
#include "library/choice.h"
#include "library/typed_expr.h"
#include "library/annotation.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/tactic/kabstract.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/elaborator.h"

namespace lean {
MK_THREAD_LOCAL_GET_DEF(type_context_cache_helper, get_tch);

static type_context_cache & get_elab_tc_cache_for(environment const & env, options const & o) {
    return get_tch().get_cache_for(env, o);
}

#define trace_elab(CODE) lean_trace("elaborator", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_detail(CODE) lean_trace("elaborator_detail", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_debug(CODE) lean_trace("elaborator_debug", scope_trace_env _scope(m_env, m_ctx); CODE)

class elaborator_exception : public formatted_exception {
public:
    elaborator_exception(expr const & e, format const & fmt):formatted_exception(e, fmt) {}
};

elaborator::elaborator(environment const & env, options const & opts, local_level_decls const & lls,
                       metavar_context const & mctx, local_context const & lctx):
    m_env(env), m_opts(opts), m_local_level_decls(lls),
    m_ctx(mctx, lctx, get_elab_tc_cache_for(env, opts), transparency_mode::Semireducible) {
}

format elaborator::pp(type_context & ctx, expr const & e) {
    formatter_factory const & factory = get_global_ios().get_formatter_factory();
    formatter fmt = factory(m_env, m_opts, ctx);
    return fmt(instantiate_mvars(e));
}

format elaborator::pp(expr const & e) {
    return pp(m_ctx, e);
}

format elaborator::pp_indent(type_context & ctx, expr const & e) {
    unsigned i = get_pp_indent(m_opts);
    return nest(i, line() + pp(ctx, e));
}

format elaborator::pp_indent(expr const & e) {
    return pp_indent(m_ctx, e);
}

format elaborator::pp(local_context const & lctx) {
    formatter_factory const & factory = get_global_ios().get_formatter_factory();
    formatter fmt = factory(m_env, m_opts, m_ctx);
    return lctx.pp(fmt);
}

static std::string pos_string_for(expr const & e) {
    pos_info_provider * provider = get_pos_info_provider();
    if (!provider) return "'unknown'";
    pos_info pos  = provider->get_pos_info_or_some(e);
    sstream s;
    s << provider->get_file_name() << ":" << pos.first << ":" << pos.second << ":";
    return s.str();
}

level elaborator::mk_univ_metavar() {
    level r = m_ctx.mk_univ_metavar_decl();
    m_uvar_stack.push_back(r);
    return r;
}

expr elaborator::mk_metavar(expr const & A) {
    expr r = copy_tag(A, m_ctx.mk_metavar_decl(m_ctx.lctx(), A));
    m_mvar_stack.push_back(r);
    return r;
}

expr elaborator::mk_type_metavar() {
    level l = mk_univ_metavar();
    return mk_metavar(mk_sort(l));
}

expr elaborator::mk_instance_core(local_context const & lctx, expr const & C) {
    optional<expr> inst = m_ctx.mk_class_instance_at(lctx, C);
    if (!inst) {
        tactic_state s = mk_tactic_state_for(m_env, m_opts, m_ctx.mctx(), lctx, C);
        throw elaborator_exception(C, format("failed to synthesize type class instance for") + line() + s.pp());
    }
    return *inst;
}

expr elaborator::mk_instance_core(expr const & C) {
    return mk_instance_core(m_ctx.lctx(), C);
}

expr elaborator::mk_instance(expr const & C) {
    if (has_expr_metavar(C)) {
        expr inst = mk_metavar(C);
        m_instance_stack.push_back(inst);
        return inst;
    } else {
        return mk_instance_core(C);
    }
}

expr elaborator::instantiate_mvars(expr const & e) {
    expr r = m_ctx.instantiate_mvars(e);
    if (r.get_tag() == nulltag)
        r.set_tag(e.get_tag());
    return r;
}

level elaborator::get_level(expr const & A) {
    return ::lean::get_level(m_ctx, A);
}

level elaborator::replace_univ_placeholder(level const & l) {
    auto fn = [&](level const & l) {
        if (is_placeholder(l))
            return some_level(mk_univ_metavar());
        else
            return none_level();
    };
    return replace(l, fn);
}

static bool contains_placeholder(level const & l) {
    bool contains = false;
    auto fn = [&](level const & l) {
        if (contains) return false;
        if (is_placeholder(l))
            contains = true;
        return true;
    };
    for_each(l, fn);
    return contains;
}

/* Here, we say a term is first-order IF all applications are of the form (f ...) where f is a constant. */
static bool is_first_order(expr const & e) {
    return !find(e, [&](expr const & e, unsigned) {
            return is_app(e) && !is_constant(get_app_fn(e));
        });
}

bool elaborator::is_elim_elab_candidate(name const & fn) {
    if (inductive::is_elim_rule(m_env, fn))
        return true;
    if (is_aux_recursor(m_env, fn))
        return true;
    if (is_user_defined_recursor(m_env, fn))
        return true;
    // TODO(Leo): add attribute for adding extra-cases,
    // and remove hard coded case
    if (fn == get_eq_subst_name())
        return true;
    return false;
}

/** See comment at elim_info */
auto elaborator::use_elim_elab_core(name const & fn) -> optional<elim_info> {
    if (!is_elim_elab_candidate(fn))
        return optional<elim_info>();
    type_context::tmp_locals locals(m_ctx);
    declaration d     = m_env.get(fn);
    expr type         = d.get_type();
    while (is_pi(type)) {
        type = instantiate(binding_body(type), locals.push_local_from_binding(type));
    }

    buffer<expr> C_args;
    expr const & C = get_app_args(type, C_args);
    if (!is_local(C) || C_args.empty() || !std::all_of(C_args.begin(), C_args.end(), is_local)) {
        trace_elab_detail(tout() << "'eliminator' elaboration is not used for '" << fn <<
                          "' because resulting type is not of the expected form\n";);
        return optional<elim_info>();
    }

    buffer<expr> const & params = locals.as_buffer();
    optional<unsigned> _midx = params.index_of(C);
    if (!_midx)
        return optional<elim_info>();

    unsigned midx = *_midx;
    buffer<unsigned> idxs;
    buffer<bool>     found;
    found.resize(C_args.size(), false);
    unsigned i    = params.size();
    unsigned nexplicit = 0;
    while (i > 0) {
        --i;
        expr const & param = params[i];

        if (!is_explicit(local_info(param))) {
            continue;
        }
        nexplicit++;

        if (optional<unsigned> pos = C_args.index_of(param)) {
            // Parameter is an argument of the resulting type (C ...)
            if (!found[*pos]) {
                // We store it if we could not infer it using the type of other arguments.
                found[*pos] = true;
                idxs.push_back(i);
            }
            continue;
        }

        expr param_type = m_ctx.infer(param);
        if (!is_first_order(param_type))
            continue;

        bool collected = false;
        for_each(param_type, [&](expr const & e, unsigned) {
                if (is_local(e)) {
                    if (optional<unsigned> pos = C_args.index_of(e)) {
                        if (!found[*pos]) {
                            collected   = true;
                            found[*pos] = true;
                        }
                    }
                }
                return true;
            });
        if (collected)
            idxs.push_back(i);
    }

    for (unsigned i = 0; i < found.size(); i++) {
        if (!found[i]) {
            trace_elab_detail(tout() << "'eliminator' elaboration is not used for '" << fn <<
                              "' because did not find a (reliable) way to synthesize '" << C_args[i] << "' " <<
                              "which occurs in the resulting type\n";);
            return optional<elim_info>();
        }
    }

    std::reverse(idxs.begin(), idxs.end());
    trace_elab_detail(tout() << "'eliminator' elaboration is going to be used for '" << fn << "' applications, "
                      << "the motive is computed using the argument(s):";
                      for (unsigned idx : idxs) tout() << " #" << (idx+1);
                      tout() << "\n";);
    return optional<elim_info>(params.size(), nexplicit, midx, to_list(idxs));
}

/** See comment at elim_info */
auto elaborator::use_elim_elab(name const & fn) -> optional<elim_info> {
    if (auto it = m_elim_cache.find(fn))
        return *it;
    optional<elim_info> r = use_elim_elab_core(fn);
    m_elim_cache.insert(fn, r);
    return r;
}

expr elaborator::ensure_function(expr const & e, expr const & ref) {
    expr e_type = whnf(infer_type(e));
    if (!is_pi(e_type)) {
        throw elaborator_exception(ref, format("function expected at") + pp_indent(e));
    }
    return e;
}

expr elaborator::ensure_type(expr const & e, expr const & ref) {
    expr e_type = whnf(infer_type(e));
    if (is_sort(e_type))
        return e;
    if (is_meta(e_type)) {
        checkpoint C(*this);
        if (is_def_eq(e_type, mk_sort(mk_univ_metavar()))) {
            C.commit();
            return e;
        }
    }
    throw elaborator_exception(ref, format("type expected at") + pp_indent(e));
}

optional<expr> elaborator::ensure_has_type(expr const & e, expr const & e_type, expr const & type) {
    if (is_def_eq(e_type, type))
        return some_expr(e);
    return none_expr();
}

expr elaborator::visit_typed_expr(expr const & e) {
    expr val          = get_typed_expr_expr(e);
    expr type         = get_typed_expr_type(e);
    expr new_type;
    {
        checkpoint C(*this);
        new_type = ensure_type(visit(type, none_expr()), type);
        process_checkpoint(C);
    }
    expr new_val      = visit(val, some_expr(new_type));
    expr new_val_type = infer_type(new_val);
    if (auto r = ensure_has_type(new_val, new_val_type, new_type))
        return *r;
    throw elaborator_exception(e,
                               format("invalid type ascription, expression has type") + pp_indent(new_val_type) +
                               line() + format(", but is expected to have type") + pp_indent(new_type));
}

expr elaborator::visit_prenum(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_prenum(e));
    mpz const & v  = prenum_value(e);
    tag e_tag      = e.get_tag();
    expr A;
    if (expected_type) {
        A = *expected_type;
        if (is_metavar(*expected_type))
            m_numeral_type_stack.push_back(A);
    } else {
        A = mk_type_metavar();
        m_numeral_type_stack.push_back(A);
    }
    level A_lvl = get_level(A);
    levels ls(A_lvl);
    if (v.is_neg())
        throw elaborator_exception(e, format("invalid pre-numeral, it must be a non-negative value"));
    if (v.is_zero()) {
        expr has_zero_A = mk_app(mk_constant(get_has_zero_name(), ls), A, e_tag);
        expr S          = mk_instance(has_zero_A);
        return mk_app(mk_app(mk_constant(get_zero_name(), ls), A, e_tag), S, e_tag);
    } else {
        expr has_one_A = mk_app(mk_constant(get_has_one_name(), ls), A, e_tag);
        expr S_one     = mk_instance(has_one_A);
        expr one       = mk_app(mk_app(mk_constant(get_one_name(), ls), A, e_tag), S_one, e_tag);
        if (v == 1) {
            return one;
        } else {
            expr has_add_A = mk_app(mk_constant(get_has_add_name(), ls), A, e_tag);
            expr S_add     = mk_instance(has_add_A);
            std::function<expr(mpz const & v)> convert = [&](mpz const & v) {
                lean_assert(v > 0);
                if (v == 1)
                    return one;
                else if (v % mpz(2) == 0) {
                    expr r = convert(v / 2);
                    return mk_app(mk_app(mk_app(mk_constant(get_bit0_name(), ls), A, e_tag), S_add, e_tag), r, e_tag);
                } else {
                    expr r = convert(v / 2);
                    return mk_app(mk_app(mk_app(mk_app(mk_constant(get_bit1_name(), ls), A, e_tag), S_one, e_tag),
                                         S_add, e_tag), r, e_tag);
                }
            };
            return convert(v);
        }
    }
}

expr elaborator::visit_sort(expr const & e) {
    expr r = update_sort(e, replace_univ_placeholder(sort_level(e)));
    if (contains_placeholder(sort_level(e)))
        m_to_check_sorts.emplace_back(e, r);
    return r;
}

expr elaborator::visit_const_core(expr const & e) {
    declaration d = m_env.get(const_name(e));
    buffer<level> ls;
    for (level const & l : const_levels(e))
        ls.push_back(replace_univ_placeholder(l));
    unsigned num_univ_params = d.get_num_univ_params();
    if (num_univ_params < ls.size()) {
        format msg("incorrect number of universe levels parameters for '");
        msg += format(const_name(e)) + format("', #") + format(num_univ_params);
        msg += format(" expected, #") + format(ls.size()) + format("provided");
        throw elaborator_exception(e, msg);
    }
    // "fill" with meta universe parameters
    for (unsigned i = ls.size(); i < num_univ_params; i++)
        ls.push_back(mk_univ_metavar());
    lean_assert(num_univ_params == ls.size());
    return update_constant(e, to_list(ls.begin(), ls.end()));
}

expr elaborator::visit_function(expr const & fn, bool has_args, expr const & ref) {
    expr r;
    switch (fn.kind()) {
    case expr_kind::Var:
    case expr_kind::App:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Pi:
    case expr_kind::Meta:
    case expr_kind::Sort:
        throw elaborator_exception(ref, format("invalid application, function expected"));
    case expr_kind::Local:     r = fn; break;
    case expr_kind::Constant:  r = visit_const_core(fn); break;
    case expr_kind::Macro:     r = visit_macro(fn, none_expr()); break;
    case expr_kind::Lambda:    r = visit_lambda(fn, none_expr()); break;
    case expr_kind::Let:       r = visit_let(fn, none_expr()); break;
    }
    if (has_args)
        r = ensure_function(r, ref);
    return r;
}

format elaborator::pp_overloads(buffer<expr> const & fns) {
    format r("overloads:");
    r += space();
    bool first = true;
    for (expr const & fn : fns) {
        if (first) first = false; else r += format(", ");
        r += pp(fn);
    }
    return paren(r);
}

void elaborator::validate_overloads(buffer<expr> const & fns, expr const & ref) {
    for (expr const & fn_i : fns) {
        if (is_constant(fn_i) && use_elim_elab(const_name(fn_i))) {
            format msg("invalid overloaded application, "
                       "elaborator has special support for '");
            msg += pp(fn_i);
            msg += format("' (it is handled as an \"eliminator\"), "
                          "but this kind of constant cannot be overloaded "
                          "(solution: use fully qualified names) ");
            msg += pp_overloads(fns);
            return throw elaborator_exception(ref, msg);
        }
    }
}

format elaborator::mk_app_type_mismatch_error(expr const & t, expr const & arg, expr const & arg_type,
                                              expr const & expected_type) {
    format msg = format("type mismatch at application");
    msg += pp_indent(t);
    msg += line() + format("term");
    msg += pp_indent(arg);
    msg += line() + format("has type");
    msg += pp_indent(arg_type);
    msg += line() + format("but is expected to have type");
    msg += pp_indent(expected_type);
    return msg;
}

format elaborator::mk_too_many_args_error(expr const & fn_type) {
    return
        format("invalid function application, too many arguments, function type:") +
        pp_indent(fn_type);
}

void elaborator::throw_app_type_mismatch(expr const & t, expr const & arg, expr const & arg_type, expr const & expected_type,
                                         expr const & ref) {
    throw elaborator_exception(ref, mk_app_type_mismatch_error(t, arg, arg_type, expected_type));
}

expr elaborator::visit_elim_app(expr const & fn, elim_info const & info, buffer<expr> const & args,
                                optional<expr> const & _expected_type, expr const & ref) {
    lean_assert(info.m_nexplicit <= args.size());
    if (!_expected_type) {
        throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) + format ("' application, ") +
                                   format("elaborator has special support for this kind of application ") +
                                   format("(it is handled as an \"eliminator\"), ") +
                                   format("but the expected type must be known"));
    }

    expr expected_type = instantiate_mvars(*_expected_type);
    if (has_expr_metavar(expected_type)) {
        throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) + format ("' application, ") +
                                   format("elaborator has special support for this kind of application ") +
                                   format("(it is handled as an \"eliminator\"), ") +
                                   format("but expected type must not contain metavariables") +
                                   pp_indent(expected_type));
    }

    trace_elab_debug(
        tout() << "eliminator elaboration for '" << fn << "'\n"
        << "  arity:     " << info.m_arity << "\n"
        << "  nexplicit: " << info.m_nexplicit << "\n"
        << "  motive:    #" << (info.m_motive_idx+1) << "\n"
        << "  major:    ";
        for (unsigned idx : info.m_explicit_idxs)
            tout() << " #" << (idx+1);
        tout() << "\n";);

    expr fn_type = try_to_pi(infer_type(fn));
    buffer<expr> new_args;

    /* In the first pass we only process the arguments at info.m_explicit_idxs */
    expr type = fn_type;
    unsigned i = 0;
    unsigned j = 0;
    list<unsigned> main_idxs = info.m_explicit_idxs;
    buffer<optional<expr>> postponed_args; // mark arguments that must be elaborated in the second pass.
    {
        checkpoint C(*this);
        while (is_pi(type)) {
            expr const & d = binding_domain(type);
            binder_info const & bi = binding_info(type);
            expr new_arg;
            optional<expr> postponed;
            if (std::find(main_idxs.begin(), main_idxs.end(), i) != main_idxs.end()) {
                new_arg = visit(args[j], some_expr(d));
                j++;
                if (has_expr_metavar(new_arg)) {
                    throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) +
                                               format ("' application, ") +
                                               format("elaborator has special support for this kind of application ") +
                                               format("(it is handled as an \"eliminator\"), ") +
                                               format("but term") + pp_indent(new_arg) +
                                               line() + format("must not contain metavariables because") +
                                               format("it is used to compute the motive"));
                }
                expr new_arg_type = infer_type(new_arg);
                if (!is_def_eq(new_arg_type, d)) {
                    throw elaborator_exception(ref, mk_app_type_mismatch_error(mk_app(fn, i+1, new_args.data()),
                                                                               new_arg, new_arg_type, d));
                }
            } else if (is_explicit(bi)) {
                new_arg   = mk_metavar(d);
                postponed = args[j];
                j++;
            } else if (bi.is_inst_implicit()) {
                new_arg = mk_instance(d);
            } else {
                new_arg = mk_metavar(d);
            }
            new_args.push_back(new_arg);
            postponed_args.push_back(postponed);
            type = try_to_pi(instantiate(binding_body(type), new_arg));
            i++;
        }

        lean_assert(new_args.size() == info.m_arity);

        /* Process extra arguments */
        for (; j < args.size(); j++) {
            new_args.push_back(visit(args[j], none_expr()));
        }
        process_checkpoint(C);
    }

    /* Compute expected_type for the recursor application without extra arguments */
    buffer<expr> extra_args;
    i = new_args.size();
    while (i > info.m_arity) {
        --i;
        expr new_arg      = instantiate_mvars(new_args[i]);
        expr new_arg_type = instantiate_mvars(infer_type(new_arg));
        expected_type     = mk_pi("_a", new_arg_type, kabstract(m_ctx, expected_type, new_arg));
        extra_args.push_back(new_arg);
    }
    new_args.shrink(i);
    std::reverse(extra_args.begin(), extra_args.end());

    // Compute motive */
    trace_elab_debug(tout() << "compute motive by using keyed-abstraction:\n  " <<
                     instantiate_mvars(type) << "\nwith\n  " <<
                     expected_type << "\n";);
    buffer<expr> keys;
    get_app_args(type, keys);
    expr motive = expected_type;
    i = keys.size();
    while (i > 0) {
        --i;
        expr k = instantiate_mvars(keys[i]);
        expr k_type    = infer_type(k);
        motive = mk_lambda("_x", k_type, kabstract(m_ctx, motive, k));
    }
    trace_elab_debug(tout() << "motive:\n  " << instantiate_mvars(motive) << "\n";);

    expr motive_arg = new_args[info.m_motive_idx];
    if (!is_def_eq(motive_arg, motive)) {
        throw elaborator_exception(ref, format("\"eliminator\" elaborator failed to compute the motive"));
    }

    /* Elaborate postponed arguments */
    for (unsigned i = 0; i < new_args.size(); i++) {
        if (optional<expr> arg = postponed_args[i]) {
            lean_assert(is_metavar(new_args[i]));
            expr new_arg_type = instantiate_mvars(infer_type(new_args[i]));
            expr new_arg      = visit(*arg, some_expr(new_arg_type));
            if (!is_def_eq(new_args[i], new_arg)) {
                throw elaborator_exception(ref, format("\"eliminator\" elaborator failed to assign explicit argument"));
            }
        }
    }

    expr r = instantiate_mvars(mk_app(mk_app(fn, new_args), extra_args));
    trace_elab_debug(tout() << "elaborated recursor:\n  " << r << "\n";);
    return r;
}

expr elaborator::visit_default_app_core(expr const & fn, arg_mask amask, buffer<expr> const & args,
                                        optional<expr> const & expected_type, bool args_already_visited,
                                        expr const & ref) {
    expr fn_type = try_to_pi(infer_type(fn));
    unsigned i = 0;
    buffer<optional<expr>> types_to_check;
    buffer<expr> new_args;
    expr type = fn_type;
    while (is_pi(type)) {
        binder_info const & bi = binding_info(type);
        expr const & d = binding_domain(type);
        expr new_arg;
        if (amask == arg_mask::Default && bi.is_strict_implicit() && i == args.size())
            break;
        if ((amask == arg_mask::Default && !is_explicit(bi)) ||
            (amask == arg_mask::Simple && !bi.is_inst_implicit() && !is_first_order(d))) {
            // implicit argument
            if (bi.is_inst_implicit())
                new_arg = mk_instance(d);
            else
                new_arg = mk_metavar(d);
            // we don't types of implicit arguments
            types_to_check.push_back(none_expr());
        } else if (i < args.size()) {
            // explicit argument
            if (args_already_visited)
                new_arg = args[i];
            else
                new_arg = visit(args[i], some_expr(d));
            types_to_check.push_back(some_expr(d));
            i++;
        } else {
            break;
        }
        new_args.push_back(new_arg);
        type = try_to_pi(instantiate(binding_body(type), new_arg));
    }

    lean_assert(new_args.size() == types_to_check.size());

    if (i != args.size()) {
        throw elaborator_exception(ref, mk_too_many_args_error(fn_type));
    }

    type_context::approximate_scope scope(m_ctx);
    for (unsigned i = 0; i < new_args.size(); i++) {
        if (optional<expr> expected_type = types_to_check[i]) {
            expr & new_arg    = new_args[i];
            expr new_arg_type = infer_type(new_arg);
            if (optional<expr> new_new_arg = ensure_has_type(new_arg, new_arg_type, *expected_type)) {
                new_arg = *new_new_arg;
            } else {
                throw elaborator_exception(ref, mk_app_type_mismatch_error(mk_app(fn, i+1, new_args.data()),
                                                                           new_arg, new_arg_type, *expected_type));
            }
        }
    }

    return mk_app(fn, new_args.size(), new_args.data());
}

expr elaborator::visit_default_app(expr const & fn, arg_mask amask, buffer<expr> const & args,
                                   optional<expr> const & expected_type, expr const & ref) {
    return visit_default_app_core(fn, amask, args, expected_type, false, ref);
}

expr elaborator::visit_overload_candidate(expr const & fn, buffer<expr> const & args,
                                          optional<expr> const & expected_type, expr const & ref) {
    return visit_default_app_core(fn, arg_mask::Default, args, expected_type, true, ref);
}

expr elaborator::visit_overloaded_app(buffer<expr> const & fns, buffer<expr> const & args,
                                      optional<expr> const & expected_type, expr const & ref) {
    trace_elab_detail(tout() << "overloaded application at " << pos_string_for(ref);
                      tout() << pp_overloads(fns) << "\n";);
    unsigned initial_inst_stack_sz = m_instance_stack.size();
    buffer<expr> new_args;
    for (expr const & arg : args) {
        new_args.push_back(visit(arg, none_expr()));
    }

    metavar_context mctx = m_ctx.mctx();
    buffer<pair<expr, metavar_context>> candidates;
    buffer<elaborator_exception> error_msgs;
    for (expr const & fn : fns) {
        try {
            checkpoint C(*this);
            m_ctx.set_mctx(mctx);
            expr c = visit_overload_candidate(fn, new_args, expected_type, ref);
            try_to_synthesize_type_class_instances(initial_inst_stack_sz);
            candidates.emplace_back(c, m_ctx.mctx());
            C.commit();
        } catch (elaborator_exception & ex) {
            error_msgs.push_back(ex);
        } catch (exception & ex) {
            error_msgs.push_back(elaborator_exception(ref, format(ex.what())));
        }
    }
    lean_assert(candidates.size() + error_msgs.size() == fns.size());

    if (candidates.empty()) {
        format r("none of the overloads is applicable");
        lean_assert(error_msgs.size() == fns.size());
        for (unsigned i = 0; i < fns.size(); i++) {
            if (i > 0) r += line();
            r += line() + format("error for") + space() + pp(fns[i]);
            r += line() + error_msgs[i].pp();
        }
        throw elaborator_exception(ref, r);
    } else if (candidates.size() > 1) {
        format r("ambiguous overload, possible interpretations");
        for (auto const & c : candidates) {
            r += pp_indent(c.first);
        }
        throw elaborator_exception(ref, r);
    } else {
        m_ctx.set_mctx(candidates[0].second);
        return candidates[0].first;
    }
}

expr elaborator::visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type) {
    arg_mask amask = arg_mask::Default;
    if (is_explicit(fn)) {
        fn   = get_explicit_arg(fn);
        amask = arg_mask::All;
    } else if (is_partial_explicit(fn)) {
        fn   = get_partial_explicit_arg(fn);
        amask = arg_mask::Simple;
    }

    bool has_args = !args.empty();

    if (is_choice(fn)) {
        buffer<expr> fns;
        if (amask != arg_mask::Default)
            throw elaborator_exception(fn, format("invalid explicit annotation, symbol is overloaded "
                                                  "(solution: use fully qualified names)"));
        for (unsigned i = 0; i < get_num_choices(fn); i++) {
            expr const & fn_i = get_choice(fn, i);
            fns.push_back(fn_i);
        }
        validate_overloads(fns, fn);
        for (expr & new_fn : fns) {
            new_fn = visit_function(new_fn, has_args, fn);
        }
        return visit_overloaded_app(fns, args, expected_type, fn);
    } else {
        expr new_fn = visit_function(fn, has_args, fn);
        /* Check if we should use a custom elaboration procedure for this application. */
        if (is_constant(new_fn) && amask == arg_mask::Default) {
            if (auto info = use_elim_elab(const_name(new_fn))) {
                if (args.size() >= info->m_nexplicit) {
                    return visit_elim_app(new_fn, *info, args, expected_type, fn);
                } else {
                    trace_elab(tout() << pos_string_for(fn) << " 'eliminator' elaboration is not used for '" << fn <<
                               "' because it is not fully applied, #" << info->m_nexplicit <<
                               " explicit arguments expected\n";);
                }
            }
        }
        return visit_default_app(new_fn, amask, args, expected_type, fn);
    }
}

expr elaborator::visit_local(expr const & e, optional<expr> const & expected_type) {
    return visit_app_core(e, buffer<expr>(), expected_type);
}

expr elaborator::visit_constant(expr const & e, optional<expr> const & expected_type) {
    return visit_app_core(e, buffer<expr>(), expected_type);
}

expr elaborator::visit_app(expr const & e, optional<expr> const & expected_type) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    return visit_app_core(fn, args, expected_type);
}

expr elaborator::visit_macro(expr const & e, optional<expr> const & expected_type) {
    if (is_as_is(e)) {
        return get_as_is_arg(e);
    } else if (is_prenum(e)) {
        return visit_prenum(e, expected_type);
    } else if (is_typed_expr(e)) {
        return visit_typed_expr(e);
    } else if (is_choice(e) || is_explicit(e) || is_partial_explicit(e)) {
        return visit_app_core(e, buffer<expr>(), expected_type);
    } else if (is_rec_fn_macro(e)) {
        // TODO(Leo)
        lean_unreachable();
    } else if (is_annotation(e)) {
        expr r = visit(get_annotation_arg(e), expected_type);
        return update_macro(e, 1, &r);
    } else {
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(visit(macro_arg(e, i), none_expr()));
        return update_macro(e, args.size(), args.data());
    }
}

static expr instantiate_rev(expr const & e, type_context::tmp_locals const & locals) {
    return instantiate_rev(e, locals.as_buffer().size(), locals.as_buffer().data());
}

expr elaborator::visit_lambda(expr const & e, optional<expr> const & expected_type) {
    type_context::tmp_locals locals(m_ctx);
    checkpoint C(*this);
    expr it = e;
    expr ex;
    bool has_expected;
    if (expected_type) {
        ex = try_to_pi(instantiate_mvars(*expected_type));
        has_expected = true;
    } else {
        has_expected = false;
    }
    while (is_lambda(it)) {
        expr d     = instantiate_rev(binding_domain(it), locals);
        expr new_d = visit(d, none_expr());
        if (has_expected) {
            if (is_pi(ex)) {
                expr ex_d = binding_domain(ex);
                checkpoint C2(*this);
                if (is_def_eq(new_d, ex_d)) {
                    C2.commit();
                }
            } else {
                has_expected = false;
            }
        }
        new_d  = ensure_type(new_d, binding_domain(it));
        expr l = locals.push_local(binding_name(it), new_d, binding_info(it));
        it = binding_body(it);
        if (has_expected && is_pi(ex)) {
            ex = try_to_pi(instantiate(binding_body(ex), l));
        }
    }
    expr b = instantiate_rev(it, locals);
    expr new_b;
    if (has_expected) {
        new_b = visit(b, some_expr(ex));
    } else {
        new_b = visit(b, none_expr());
    }
    process_checkpoint(C);
    expr r = locals.mk_lambda(new_b);
    return r;
}

expr elaborator::visit_pi(expr const & e) {
    type_context::tmp_locals locals(m_ctx);
    checkpoint C(*this);
    expr it = e;
    while (is_pi(it)) {
        expr d     = instantiate_rev(binding_domain(it), locals);
        expr new_d = visit(d, none_expr());
        new_d      = ensure_type(new_d, binding_domain(it));
        locals.push_local(binding_name(it), new_d, binding_info(it));
        it = binding_body(it);
    }
    expr b     = instantiate_rev(it, locals);
    expr new_b = visit(b, none_expr());
    new_b      = ensure_type(new_b, it);
    process_checkpoint(C);
    expr r = locals.mk_pi(new_b);
    return r;
}

expr elaborator::visit_let(expr const & e, optional<expr> const & expected_type) {
    // TODO(Leo)
    lean_unreachable();
}

expr elaborator::visit_placeholder(expr const & e, optional<expr> const & expected_type) {
    if (expected_type)
        return mk_metavar(*expected_type);
    else
        return mk_metavar(mk_type_metavar());
}

expr elaborator::visit(expr const & e, optional<expr> const & expected_type) {
    if (is_placeholder(e)) {
        return visit_placeholder(e, expected_type);
    } else {
        switch (e.kind()) {
        case expr_kind::Var:        lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Meta:       return e;
        case expr_kind::Sort:       return visit_sort(e);
        case expr_kind::Local:      return visit_local(e, expected_type);
        case expr_kind::Constant:   return visit_constant(e, expected_type);
        case expr_kind::Macro:      return visit_macro(e, expected_type);
        case expr_kind::Lambda:     return visit_lambda(e, expected_type);
        case expr_kind::Pi:         return visit_pi(e);
        case expr_kind::App:        return visit_app(e, expected_type);
        case expr_kind::Let:        return visit_let(e, expected_type);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

expr elaborator::get_default_numeral_type() {
    // TODO(Leo): allow user to modify default?
    return mk_constant(get_nat_name());
}

void elaborator::ensure_numeral_types_assigned(checkpoint const & C) {
    for (unsigned i = C.m_numeral_type_stack_sz; i < m_numeral_type_stack.size(); i++) {
        expr A = instantiate_mvars(m_numeral_type_stack[i]);
        if (is_metavar(A)) {
            if (!assign_mvar(A, get_default_numeral_type()))
                throw elaborator_exception(A, format("invalid numeral, failed to force numeral to be a nat"));
        }
    }
}

void elaborator::synthesize_type_class_instances_core(unsigned old_sz, bool force) {
    unsigned j = old_sz;
    for (unsigned i = old_sz; i < m_instance_stack.size(); i++) {
        lean_assert(is_metavar(m_instance_stack[i]));
        metavar_decl mdecl = *m_ctx.mctx().get_metavar_decl(m_instance_stack[i]);
        expr inst          = instantiate_mvars(m_instance_stack[i]);
        if (!has_expr_metavar(inst)) {
            trace_elab(tout() << "skipping type class resolution at " << pos_string_for(m_instance_stack[i])
                       << ", placeholder instantiated using type inference\n";);
            continue;
        }
        expr inst_type = instantiate_mvars(infer_type(inst));
        if (!has_expr_metavar(inst_type)) {
            // We must try to synthesize instance using the local context where it was declared
            if (!is_def_eq(inst, mk_instance_core(mdecl.get_context(), inst_type)))
                throw elaborator_exception(m_instance_stack[i],
                                           format("failed to assign type class instance to placeholder"));
        } else {
            if (force) {
                throw elaborator_exception(m_instance_stack[i],
                                           format("type class instance cannot be synthesized, type has metavariables") +
                                           pp_indent(inst_type));
            } else {
                m_instance_stack[j] = m_instance_stack[i];
                j++;
            }
        }
    }
    if (!force)
        m_instance_stack.shrink(j);
}

void elaborator::invoke_tactics(checkpoint const & C) {
    // TODO(Leo)
}

void elaborator::ensure_no_unassigned_metavars(checkpoint const & C) {
}

void elaborator::process_checkpoint(checkpoint const & C) {
    ensure_numeral_types_assigned(C);
    synthesize_type_class_instances(C);
    invoke_tactics(C);
    ensure_no_unassigned_metavars(C);
}

elaborator::checkpoint::checkpoint(elaborator & e):
    m_elaborator(e),
    m_commit(false),
    m_uvar_stack_sz(e.m_uvar_stack.size()),
    m_mvar_stack_sz(e.m_mvar_stack.size()),
    m_instance_stack_sz(e.m_instance_stack.size()),
    m_numeral_type_stack_sz(e.m_numeral_type_stack.size()) {
}

elaborator::checkpoint::~checkpoint() {
    if (!m_commit) {
        m_elaborator.m_uvar_stack.shrink(m_uvar_stack_sz);
        m_elaborator.m_mvar_stack.shrink(m_mvar_stack_sz);
        m_elaborator.m_instance_stack.shrink(m_instance_stack_sz);
        m_elaborator.m_numeral_type_stack.shrink(m_numeral_type_stack_sz);
    }
}

void elaborator::checkpoint::commit() {
    m_commit = true;
}

std::tuple<expr, level_param_names> elaborator::operator()(expr const & e) {
    checkpoint C(*this);
    expr r = visit(e,  none_expr());
    process_checkpoint(C);
    r = instantiate_mvars(r);
    // TODO(Leo)
    level_param_names ls;
    return std::make_tuple(r, ls);
}

std::tuple<expr, level_param_names> elaborate(environment const & env, options const & opts, local_level_decls const & lls,
                                              metavar_context & mctx, local_context const & lctx, expr const & e) {
    elaborator elab(env, opts, lls, mctx, lctx);
    auto r = elab(e);
    mctx = elab.mctx();
    return r;
}

void initialize_elaborator() {
    register_trace_class("elaborator");
    register_trace_class("elaborator_detail");
    register_trace_class("elaborator_debug");
}

void finalize_elaborator() {
}
}
