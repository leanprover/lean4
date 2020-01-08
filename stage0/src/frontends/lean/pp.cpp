/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include <limits>
#include <string>
#include "runtime/utf8.h"
#include "runtime/flet.h"
#include "util/fresh_name.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/sorry.h"
#include "library/annotation.h"
#include "library/aliases.h"
#include "library/class.h"
#include "library/expr_pair.h"
#include "library/placeholder.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/explicit.h"
#include "library/num.h"
#include "library/util.h"
#include "library/print.h"
#include "library/pp_options.h"
#include "library/constants.h"
#include "library/replace_visitor.h"
#include "library/string.h"
#include "library/type_context.h"
#include "library/idx_metavar.h"
#include "library/equations_compiler/equations.h"
#include "library/tactic/tactic_state.h"
#include "library/compiler/util.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/util.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/typed_expr.h"

#include "library/trace.h"

namespace lean {
static format * g_ellipsis_n_fmt  = nullptr;
static format * g_ellipsis_fmt    = nullptr;
static format * g_placeholder_fmt = nullptr;
static format * g_lambda_n_fmt    = nullptr;
static format * g_lambda_fmt      = nullptr;
static format * g_forall_n_fmt    = nullptr;
static format * g_forall_fmt      = nullptr;
static format * g_arrow_n_fmt     = nullptr;
static format * g_arrow_fmt       = nullptr;
static format * g_let_fmt         = nullptr;
static format * g_in_fmt          = nullptr;
static format * g_assign_fmt      = nullptr;
static format * g_have_fmt        = nullptr;
static format * g_from_fmt        = nullptr;
static format * g_visible_fmt     = nullptr;
static format * g_show_fmt        = nullptr;
static format * g_explicit_fmt    = nullptr;
static format * g_partial_explicit_fmt    = nullptr;

class nat_numeral_pp {
    name m_nat;
    expr m_nat_zero;
    expr m_nat_succ;
public:
    nat_numeral_pp():
        m_nat(get_nat_name()),
        m_nat_zero(mk_constant(get_nat_zero_name())),
        m_nat_succ(mk_constant(get_nat_succ_name())) {
    }

    // Return an unsigned if \c e if of the form (succ^k zero), and k
    // fits in a machine unsigned integer.
    optional<unsigned> to_unsigned(expr const & e) const {
        unsigned r = 0;
        expr const * it = &e;
        while (true) {
            if (*it == m_nat_zero) {
                return optional<unsigned>(r);
            } else if (is_app(*it) && app_fn(*it) == m_nat_succ) {
                if (r == std::numeric_limits<unsigned>::max())
                    return optional<unsigned>(); // just in case, it does not really happen in practice
                r++;
                it = &app_arg(*it);
            } else if (is_zero(get_app_fn(*it))) {
                return optional<unsigned>(r);
            } else {
                return optional<unsigned>();
            }
        }
    }
};

static nat_numeral_pp * g_nat_numeral_pp = nullptr;

static optional<unsigned> to_unsigned(expr const & e) {
    return g_nat_numeral_pp->to_unsigned(e);
}

void initialize_pp() {
    g_ellipsis_n_fmt  = new format(format("…"));
    g_ellipsis_fmt    = new format(format("..."));
    g_placeholder_fmt = new format(format("_"));
    g_lambda_n_fmt    = new format(format("λ"));
    g_lambda_fmt      = new format(format("fun"));
    g_forall_n_fmt    = new format(format("∀"));
    g_forall_fmt      = new format(format("forall"));
    g_arrow_n_fmt     = new format(format("→"));
    g_arrow_fmt       = new format(format("->"));
    g_let_fmt         = new format(format("let"));
    g_in_fmt          = new format(format("in"));
    g_assign_fmt      = new format(format(":="));
    g_have_fmt        = new format(format("have"));
    g_from_fmt        = new format(format("from"));
    g_visible_fmt     = new format(format("[visible]"));
    g_show_fmt        = new format(format("show"));
    g_explicit_fmt    = new format(format("@"));
    g_partial_explicit_fmt    = new format(format("@@"));
    g_nat_numeral_pp  = new nat_numeral_pp();
}

void finalize_pp() {
    delete g_nat_numeral_pp;
    delete g_ellipsis_n_fmt;
    delete g_ellipsis_fmt;
    delete g_placeholder_fmt;
    delete g_lambda_n_fmt;
    delete g_lambda_fmt;
    delete g_forall_n_fmt;
    delete g_forall_fmt;
    delete g_arrow_n_fmt;
    delete g_arrow_fmt;
    delete g_let_fmt;
    delete g_in_fmt;
    delete g_assign_fmt;
    delete g_have_fmt;
    delete g_from_fmt;
    delete g_visible_fmt;
    delete g_show_fmt;
    delete g_partial_explicit_fmt;
    delete g_explicit_fmt;
}

/** \brief We assume a metavariable name has a suggestion embedded in it WHEN its
    last component is a string. */
static bool has_embedded_suggestion(name const & m) {
    return m.is_string();
}

/** \see extract_suggestion */
static name extract_suggestion_core(name const & m) {
    if (m.is_string()) {
        if (m.is_atomic())
            return m;
        else
            return name(extract_suggestion_core(m.get_prefix()), m.get_string());
    } else {
        return name();
    }
}

/** \brief Extract "suggested name" embedded in a metavariable name

    \pre has_embedded_suggestion(m)
*/
static name extract_suggestion(name const & m) {
    lean_assert(has_embedded_suggestion(m));
    name r = extract_suggestion_core(m);
    lean_assert(!r.is_anonymous());
    return r;
}

name pretty_fn::mk_metavar_name(name const & m, optional<name> const & prefix) {
    if (auto it = m_purify_meta_table.find(m))
        return *it;
    if (has_embedded_suggestion(m)) {
        name suggested = extract_suggestion(m);
        name r         = suggested;
        unsigned i     = 1;
        while (m_purify_used_metas.contains(r)) {
            r = suggested.append_after(i);
            i++;
        }
        m_purify_used_metas.insert(r);
        m_purify_meta_table.insert(m, r);
        return r;
    } else {
        name new_m;
        if (prefix)
            new_m = prefix->append_after(m_next_meta_idx);
        else
            new_m = m_meta_prefix.append_after(m_next_meta_idx);
        m_next_meta_idx++;
        m_purify_meta_table.insert(m, new_m);
        return new_m;
    }
}

name pretty_fn::mk_local_name(name const & n, name const & suggested) {
    if (!m_purify_locals)
        return suggested;
    if (auto it = m_purify_local_table.find(n))
        return *it;
    unsigned i = 1;
    name r = suggested;
    while (m_purify_used_locals.contains(r)) {
        r = suggested.append_after(i);
        i++;
    }
    m_purify_used_locals.insert(r);
    m_purify_local_table.insert(n, r);
    return r;
}

level pretty_fn::purify(level const & l) {
    if (!m_universes || !m_purify_metavars || !has_mvar(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_mvar(l))
                return some_level(l);
            if (is_metavar_decl_ref(l))
                return some_level(mk_univ_mvar(mk_metavar_name(mvar_id(l), "l")));
            if (is_mvar(l) && !is_idx_metauniv(l))
                return some_level(mk_univ_mvar(mk_metavar_name(mvar_id(l))));
            return none_level();
        });
}

expr pretty_fn::infer_type(expr const & e) {
    try {
        return m_ctx.infer(e);
    } catch (exception &) {
        expr dummy = mk_Prop();
        return dummy;
    }
}

/** \brief Make sure that all metavariables have reasonable names,
    and for all local constants l1 l2, mlocal_pp_name(l1) != mlocal_pp_name(l2).

    \remark pretty_fn will create new local constants when pretty printing,
    but it will make sure that the new constants will not produce collisions.

    \remark We do not purify metavariable names IF the user provided them.
    We use the test (mlocal_name(e) == mlocal_pp_name(e)) to decide whether
    the user provided the name or not.
*/
expr pretty_fn::purify(expr const & e) {
    if (!has_expr_metavar(e) && !has_local(e) && (!m_universes || !has_univ_metavar(e)))
        return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_local(e) && (!m_universes || !has_univ_metavar(e))) {
                return some_expr(e);
            } else if (m_purify_metavars && is_metavar_decl_ref(e)) {
                return some_expr(mk_metavar(mk_metavar_name(mvar_name(e), "m")));
            } else if (m_purify_metavars && is_metavar(e) && !is_idx_metavar(e)) {
                return some_expr(mk_metavar(mk_metavar_name(mvar_name(e))));
            } else if (is_local(e)) {
                return some_expr(mk_local(local_name(e), mk_local_name(local_name(e), local_pp_name(e)),
                                          infer_type(e), local_info(e)));
            } else if (is_constant(e)) {
                return some_expr(update_constant(e, map(const_levels(e), [&](level const & l) { return purify(l); })));
            } else if (is_sort(e)) {
                return some_expr(update_sort(e, purify(sort_level(e))));
            } else {
                return none_expr();
            }
        });
}

void pretty_fn::set_options_core(options const & _o) {
    options o = _o;
    bool all          = get_pp_all(o);
    if (all) {
        o = o.update_if_undef(get_pp_implicit_name(), true);
        o = o.update_if_undef(get_pp_proofs_name(), true);
        o = o.update_if_undef(get_pp_coercions_name(), true);
        o = o.update_if_undef(get_pp_notation_name(), false);
        o = o.update_if_undef(get_pp_universes_name(), true);
        o = o.update_if_undef(get_pp_full_names_name(), true);
        o = o.update_if_undef(get_pp_beta_name(), false);
        o = o.update_if_undef(get_pp_numerals_name(), false);
        o = o.update_if_undef(get_pp_strings_name(), false);
        o = o.update_if_undef(get_pp_binder_types_name(), true);
    }
    m_options           = o;
    m_indent            = get_pp_indent(o);
    m_max_depth         = get_pp_max_depth(o);
    m_max_steps         = get_pp_max_steps(o);
    m_implict           = get_pp_implicit(o);
    m_proofs            = get_pp_proofs(o);
    m_unicode           = get_pp_unicode(o);
    m_coercion          = get_pp_coercions(o);
    m_notation          = get_pp_notation(o);
    m_universes         = get_pp_universes(o);
    m_full_names        = get_pp_full_names(o);
    m_private_names     = get_pp_private_names(o);
    m_purify_metavars   = get_pp_purify_metavars(o);
    m_purify_locals     = get_pp_purify_locals(o);
    m_locals_full_names = get_pp_locals_full_names(o);
    m_beta              = get_pp_beta(o);
    m_numerals          = get_pp_numerals(o);
    m_strings           = get_pp_strings(o);
    m_preterm           = get_pp_preterm(o);
    m_binder_types      = get_pp_binder_types(o);
    m_hide_comp_irrel   = get_pp_hide_comp_irrel(o);
    m_annotations       = get_pp_annotations(o);
    m_compact_let       = get_pp_compact_let(o);
    m_hide_full_terms   = get_formatter_hide_full_terms(o);

    m_num_nat_coe       = m_numerals;
    m_structure_instances = get_pp_structure_instances(o);
    m_structure_instances_qualifier = get_pp_structure_instances_qualifier(o);
    m_structure_projections         = get_pp_structure_projections(o);
}

void pretty_fn::set_options(options const & o) {
    if (is_eqp(o, m_options))
        return;
    set_options_core(o);
}

format pretty_fn::pp_child(level const & l) {
    if (is_explicit(l) || is_param(l) || is_mvar(l)) {
        return pp_level(l);
    } else {
        return paren(pp_level(l));
    }
}

format pretty_fn::pp_max(level l) {
    lean_assert(is_max(l) || is_imax(l));
    format r  = format(is_max(l) ? "max" : "imax");
    level lhs = is_max(l) ? max_lhs(l) : imax_lhs(l);
    level rhs = is_max(l) ? max_rhs(l) : imax_rhs(l);
    r += nest(m_indent, compose(line(), pp_child(lhs)));
    while (kind(rhs) == kind(l)) {
        l = rhs;
        lhs = is_max(l) ? max_lhs(l) : imax_lhs(l);
        rhs = is_max(l) ? max_rhs(l) : imax_rhs(l);
        r += nest(m_indent, compose(line(), pp_child(lhs)));
    }
    r += nest(m_indent, compose(line(), pp_child(rhs)));
    return group(r);
}

format pretty_fn::pp_meta(level const & l) {
    if (m_universes) {
        if (is_idx_metauniv(l)) {
            return format((sstream() << "?u_" << to_meta_idx(l)).str());
        } else if (is_metavar_decl_ref(l)) {
            return format((sstream() << "?l_" << get_metavar_decl_ref_suffix(l)).str());
        } else {
            return compose(format("?"), format(mvar_id(l)));
        }
    } else {
        return format("?");
    }
}

format pretty_fn::pp_level(level const & l) {
    if (is_explicit(l)) {
        return format(get_depth(l));
    } else {
        switch (kind(l)) {
        case level_kind::Zero:
            lean_unreachable(); // LCOV_EXCL_LINE
        case level_kind::Param:
            return format(param_id(l));
        case level_kind::MVar:
            return pp_meta(l);
        case level_kind::Succ: {
            auto p = to_offset(l);
            return pp_child(p.first) + format("+") + format(p.second);
        }
        case level_kind::Max: case level_kind::IMax:
            return pp_max(l);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

bool pretty_fn::is_implicit(expr const & f) {
    // Remark: we assume preterms do not have implicit arguments,
    // since they have not been elaborated yet.
    // Moreover, the type checker will probably produce an error
    // when trying to infer type information
    if (m_implict || m_preterm)
        return false; // showing implicit arguments
    if (has_loose_bvars(f)) {
        // the Lean type checker assumes expressions are closed.
        return false;
    }
    try {
        expr t = m_ctx.relaxed_whnf(m_ctx.infer(f));
        if (is_pi(t)) {
            binder_info bi = binding_info(t);
            return !is_explicit(bi);
        } else {
            return false;
        }
    } catch (exception &) {
        return false;
    }
}

bool pretty_fn::is_default_arg_app(expr const & e) {
    if (m_implict || m_preterm)
        return false; // showing default arguments
    if (has_loose_bvars(app_fn(e))) {
        // the Lean type checker assumes expressions are closed.
        return false;
    }
    try {
        expr t = m_ctx.relaxed_whnf(m_ctx.infer(app_fn(e)));
        if (is_pi(t)) {
            expr arg_type = binding_domain(t);
            t = binding_body(t);
            if (!is_pi(t) && !is_var(t) && is_app_of(arg_type, get_opt_param_name(), 2)) {
                expr defval = app_arg(arg_type);
                return !has_loose_bvars(defval) && defval == app_arg(e);
            }
        }
    } catch (exception &) { }
    return false;
}

bool pretty_fn::is_prop(expr const & e) {
    try {
        expr t = m_ctx.relaxed_whnf(m_ctx.infer(e));
        return t == mk_Prop();
    } catch (exception &) {
        return false;
    }
}

auto pretty_fn::add_paren_if_needed(result const & r, unsigned bp) -> result {
    if (r.rbp() < bp) {
        return result(paren(r.fmt()));
    } else {
        return r;
    }
}

auto pretty_fn::pp_child_core(expr const & e, unsigned bp, bool ignore_hide) -> result {
    return add_paren_if_needed(pp(e, ignore_hide), bp);
}

static bool is_coercion(expr const & e) {
    return is_app_of(e, get_coe_name()) && get_app_num_args(e) >= 4;
}

static bool is_coercion_fn(expr const & e) {
    return is_app_of(e, get_coe_fn_name()) && get_app_num_args(e) >= 3;
}

auto pretty_fn::pp_hide_coercion(expr const & e, unsigned bp, bool ignore_hide) -> result {
    lean_assert(is_coercion(e));
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() == 4) {
        return pp_child(args[3], bp, ignore_hide);
    } else {
        expr new_e = mk_app(args.size() - 3, args.data() + 3);
        return pp_child(new_e, bp, ignore_hide);
    }
}

auto pretty_fn::pp_hide_coercion_fn(expr const & e, unsigned bp, bool ignore_hide) -> result {
    lean_assert(is_coercion_fn(e));
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() == 3) {
        return pp_child(args[2], bp, ignore_hide);
    } else {
        expr new_e = mk_app(args.size() - 2, args.data() + 2);
        return pp_child(new_e, bp, ignore_hide);
    }
}

auto pretty_fn::pp_child(expr const & e, unsigned bp, bool ignore_hide) -> result {
    if (is_app(e)) {
        if (m_numerals) {
            if (auto n = to_num(e)) return pp_num(*n, bp);
        }
        if (m_strings) {
            if (auto r = to_string(e)) return pp_string_literal(*r);
            if (auto r = to_char(m_ctx, e)) return pp_char_literal(*r);
        }
        expr const & f = app_fn(e);
        if (is_implicit(f)) {
            return pp_child(f, bp, ignore_hide);
        } else if (!m_coercion && is_coercion(e)) {
            return pp_hide_coercion(e, bp, ignore_hide);
        } else if (!m_coercion && is_coercion_fn(e)) {
            return pp_hide_coercion_fn(e, bp, ignore_hide);
        }
    }
    return pp_child_core(e, bp, ignore_hide);
}

auto pretty_fn::pp_var(expr const & e) -> result {
    return result(compose(format("#"), format(bvar_idx(e).to_std_string())));
}

auto pretty_fn::pp_sort(expr const & e) -> result {
    level u = sort_level(e);
    if (u == mk_level_zero()) {
        return result(format("Prop"));
    } else if (u == mk_level_one()) {
        return result(format("Type"));
    } else if (optional<level> u1 = dec_level(u)) {
        return result(max_bp()-1, group(format("Type") + space() + nest(5, pp_child(*u1))));
    } else {
        return result(max_bp()-1, group(format("Sort") + space() + nest(5, pp_child(u))));
    }
}

optional<name> pretty_fn::is_aliased(name const & n) const {
    if (auto it = is_expr_aliased(m_env, n)) {
        // must check if we are not shadow by current namespace
        for (name const & ns : get_namespaces(m_env)) {
            if (!ns.is_anonymous() && m_env.find(ns + *it))
                return optional<name>();
        }
        return it;
    } else {
        return optional<name>();
    }
}

format pretty_fn::escape(name const & n) {
    // also escape keyword-like names
    if (n.is_atomic() && n.is_string() && find(m_token_table, n.get_string().data())) { // HACK: accessing Lean string as C String
        sstream ss;
        ss << "«" << n.get_string().to_std_string() << "»";
        return format(ss.str());
    }
    return format(n.escape());
}

auto pretty_fn::pp_const(expr const & e, optional<unsigned> const & num_ref_univ_params) -> result {
    if (is_enf_neutral(e) && m_unicode)
        return format("◾");
    if (is_enf_unreachable(e) && m_unicode)
        return format("⊥");
    name n = const_name(e);
    if (m_notation && n == get_unit_unit_name())
        return format("()");
    // Remark: if num_ref_univ_params is "some", then it contains the number of
    // universe levels that are fixed in a section. That is, \c e corresponds to
    // a constant in a section which has fixed levels.
    auto short_n = n;
    if (!m_full_names) {
        if (auto it = is_aliased(n)) {
            if (!m_private_names || !private_to_user_name(n))
                short_n = *it;
        } else {
            for (name const & ns : get_namespaces(m_env)) {
                if (!ns.is_anonymous()) {
                    name new_n = n.replace_prefix(ns, name());
                    if (new_n != n &&
                        !new_n.is_anonymous() &&
                        (!new_n.is_atomic() || !is_protected(m_env, n))) {
                        short_n = new_n;
                        break;
                    }
                }
            }
        }
    }
    if (!m_private_names) {
        if (auto n1 = private_to_user_name(short_n))
            short_n = *n1;
    }
/*
    if (m_ctx.is_local_user_name(short_n.get_root())) {
        if (m_ctx.is_local_user_name(n.get_root())) {
            n = get_root_tk() + n;
        }
    } else {
*/
    n = short_n;
/*
    }
*/
    if (m_universes && !empty(const_levels(e))) {
        unsigned first_idx = 0;
        buffer<level> ls;
        to_buffer(const_levels(e), ls);
        if (num_ref_univ_params) {
            if (ls.size() <= *num_ref_univ_params)
                return result(escape(n));
            else
                first_idx = *num_ref_univ_params;
        }
        format r = compose(escape(n), format(".{"));
        bool first = true;
        for (unsigned i = first_idx; i < ls.size(); i++) {
            level const & l = ls[i];
            format l_fmt = pp_level(l);
            if (is_max(l) || is_imax(l))
                l_fmt = paren(l_fmt);
            if (first)
                r += nest(m_indent, l_fmt);
            else
                r += nest(m_indent, compose(line(), l_fmt));
            first = false;
        }
        r += format("}");
        return result(group(r));
    } else {
        return result(escape(n));
    }
}

auto pretty_fn::pp_meta(expr const & e) -> result {
    if (is_idx_metavar(e)) {
        return result(format((sstream() << "?x_" << to_meta_idx(e)).str()));
    } else if (is_metavar_decl_ref(e) && !m_purify_metavars) {
        return result(format((sstream() << "?m_" << get_metavar_decl_ref_suffix(e)).str()));
    } else if (m_purify_metavars) {
        return result(compose(format("?"), format(mvar_name(e))));
    } else {
        return result(compose(format("?M."), format(mvar_name(e))));
    }
}

auto pretty_fn::pp_fvar(expr const & e) -> result {
    if (optional<name> n0 = m_ctx.get_local_pp_name(e)) {
        name n = sanitize_if_fresh(*n0);
        n = sanitize_name_generator_name(n);
        if (m_locals_full_names)
            return result(format("<") + format(n + local_name(e)) + format(">"));
        else
            return format(escape(n));
    }
    return format(fvar_name(e));
}

auto pretty_fn::pp_local(expr const & e) -> result {
    name n = sanitize_if_fresh(local_pp_name(e));
    n = sanitize_name_generator_name(n);
    if (m_locals_full_names)
        return result(format("<") + format(n + local_name(e)) + format(">"));
    else
        return format(escape(n));
}

bool pretty_fn::has_implicit_args(expr const & f) {
    if (has_loose_bvars(f) || m_preterm) {
        // The Lean type checker assumes expressions are closed.
        // If preterms are being processed, then we assume
        // there are no implicit arguments.
        return false;
    }
    try {
        expr type = m_ctx.relaxed_whnf(m_ctx.infer(f));
        push_local_fn push_local(m_ctx);
        while (is_pi(type)) {
            binder_info bi = binding_info(type);
            if (!is_explicit(bi))
                return true;
            expr local = push_local(binding_name(type), binding_domain(type), binding_info(type));
            type = m_ctx.relaxed_whnf(instantiate(binding_body(type), local));
        }
        return false;
    } catch (exception &) {
        return false;
    }
}

static bool is_structure_instance(environment const & env, expr const & e, bool implicit) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn)) return false;
    name const & mk_name = const_name(fn);
    if (!is_constructor(env, mk_name)) return false;
    name const & S       = mk_name.get_prefix();
    if (!is_structure(env, S)) return false;
    /* If implicit arguments is true, and the structure has parameters, we should not
       pretty print using { ... }, because we will not be able to see the parameters. */
    if (implicit && env.get(S).to_inductive_val().get_nparams() > 0) return false;
    /* check whether it is a partially applied constructor application */
    if (get_app_num_args(e) != get_arity(env.get(mk_name).get_type())) return false;
    return true;
}

auto pretty_fn::pp_structure_instance(expr const & e) -> result {
    lean_assert(is_structure_instance(m_env, e, m_implict));
    buffer<expr> args;
    expr const & mk = get_app_args(e, args);
    name const & S  = const_name(mk).get_prefix();
    unsigned num_params = m_env.get(S).to_inductive_val().get_nparams();
    auto fields = get_structure_fields(m_env, S);
    lean_assert(args.size() == num_params + fields.size());
    format r;
    if (m_structure_instances_qualifier)
        r += format(S) + space() + format(".");
    for (unsigned i = 0; i < fields.size(); i++) {
        if (i > 0 || m_structure_instances_qualifier) r += line();
        name fname          = fields[i];
        unsigned field_size = fname.utf8_size();
        format fval_fmt     = pp_child(args[i + num_params], 0).fmt();
        if (i < fields.size() - 1) fval_fmt += format(",");
        r                  += format(fname) + space() + *g_assign_fmt + space() + nest(field_size + 4, fval_fmt);
    }
    r = group(nest(1, format("{") + r + format("}")));
    return result(r);
}

bool pretty_fn::is_field_notation_candidate(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f)) return false;
    optional<projection_info> info = get_projection_info(m_env, const_name(f));
    if (!info) return false; /* it is not a projection */
    if (get_app_num_args(e) != info->get_nparams() + 1) return false;
    /* If implicit arguments is true, and the structure has parameters, we should not
       pretty print using field notation because we will not be able to see the parameters. */
    if (m_implict && info->get_nparams()) return false;
    /* The @ explicitness annotation cannot be combined with field notation, so fail on implicit args */
    if (m_implict && has_implicit_args(e)) return false;
    name const & S = const_name(f).get_prefix();
    /* We should not use field notation with type classes since the structure is implicit. */
    if (is_class(m_env, S)) return false;
    return true;
}

auto pretty_fn::pp_field_notation(expr const & e) -> result {
    lean_assert(is_field_notation_candidate(e));
    buffer<expr> args;
    expr const & f   = get_app_args(e, args);
    bool ignore_hide = true;
    format s_fmt     = pp_child(args.back(), max_bp(), ignore_hide).fmt();
    return result(max_bp()-1, s_fmt + format(".") + format(const_name(f).get_string()));
}

auto pretty_fn::pp_app(expr const & e) -> result {
    if (is_default_arg_app(e))
        return pp_child(app_fn(e), max_bp());
    expr const & fn = app_fn(e);
    if (m_structure_instances && is_structure_instance(m_env, e, m_implict))
        return pp_structure_instance(e);
    if (m_structure_projections && is_field_notation_candidate(e))
        return pp_field_notation(e);
    // If the application contains a metavariable, then we want to
    // show the function, otherwise it would be hard to understand the
    // context where the metavariable occurs. This is hack to implement
    // formatter.hide_full_terms
    bool ignore_hide = true;
    result res_fn    = pp_child(fn, max_bp()-1, ignore_hide);
    format fn_fmt    = res_fn.fmt();
    if (m_implict && !is_app(fn) && has_implicit_args(fn))
        fn_fmt = compose(*g_explicit_fmt, fn_fmt);
    result res_arg = pp_child(app_arg(e), max_bp());
    return result(max_bp()-1, group(compose(fn_fmt, nest(m_indent, compose(line(), res_arg.fmt())))));
}

format pretty_fn::pp_binder(expr const & local) {
    format r;
    auto bi = local_info(local);
    if (!is_default(bi))
        r += format(open_binder_string(bi, m_unicode));
    r += escape(local_pp_name(local));
    if (m_binder_types) {
        r += space();
        r += compose(format(":"), nest(m_indent, compose(line(), pp_child(local_type(local), 0).fmt())));
    }
    if (!is_default(bi))
        r += format(close_binder_string(bi, m_unicode));
    return r;
}

format pretty_fn::pp_binder_block(buffer<name> const & names, expr const & type, binder_info bi) {
    format r;
    if (m_binder_types || !is_default(bi))
        r += format(open_binder_string(bi, m_unicode));
    for (name const & n : names) {
        r += escape(n);
    }
    if (m_binder_types) {
        r += space();
        r += compose(format(":"), nest(m_indent, compose(line(), pp_child(type, 0).fmt())));
    }
    if (m_binder_types || !is_default(bi))
        r += format(close_binder_string(bi, m_unicode));
    return group(r);
}

format pretty_fn::pp_binders(buffer<expr> const & locals) {
    unsigned num     = locals.size();
    buffer<name> names;
    expr local       = locals[0];
    expr   type      = local_type(local);
    binder_info bi   = local_info(local);
    names.push_back(local_pp_name(local));
    format r;
    for (unsigned i = 1; i < num; i++) {
        expr local = locals[i];
        if (!is_inst_implicit(bi) && local_type(local) == type && local_info(local) == bi) {
            names.push_back(local_pp_name(local));
        } else {
            r += group(compose(line(), pp_binder_block(names, type, bi)));
            names.clear();
            type = local_type(local);
            bi   = local_info(local);
            names.push_back(local_pp_name(local));
        }
    }
    r += group(compose(line(), pp_binder_block(names, type, bi)));
    return r;
}

auto pretty_fn::pp_lambda(expr const & e) -> result {
    expr b = e;
    buffer<expr> locals;
    while (is_lambda(b)) {
        auto p = binding_body_fresh(b, true);
        locals.push_back(p.second);
        b = p.first;
    }
    format r = m_unicode ? *g_lambda_n_fmt : *g_lambda_fmt;
    r += pp_binders(locals);
    r += group(compose(format(","), nest(m_indent, compose(line(), pp_child(b, 0).fmt()))));
    return result(0, r);
}

/** \brief Similar to #is_arrow, but only returns true if binder_info is the default one.
    That is, we don't want to lose binder info when pretty printing.
*/
static bool is_default_arrow(expr const & e) {
    return is_arrow(e) && is_default(binding_info(e));
}

auto pretty_fn::pp_pi(expr const & e) -> result {
    if (is_default_arrow(e)) {
        result lhs = pp_child(binding_domain(e), get_arrow_prec());
        expr   b   = lift_loose_bvars(binding_body(e), 1);
        result rhs = is_pi(b) ? pp(b) : pp_child(b, get_arrow_prec()-1);
        format r   = group(lhs.fmt() + space() + (m_unicode ? *g_arrow_n_fmt : *g_arrow_fmt) + line() + rhs.fmt());
        return result(get_arrow_prec(), get_arrow_prec()-1, r);
    } else {
        expr b = e;
        buffer<expr> locals;
        while (is_pi(b) && !is_default_arrow(b)) {
            auto p = binding_body_fresh(b, true);
            locals.push_back(p.second);
            b = p.first;
        }
        format r;
        r = m_unicode ? *g_forall_n_fmt : *g_forall_fmt;
        r += pp_binders(locals);
        r += group(compose(format(","), nest(m_indent, compose(line(), pp_child(b, 0).fmt()))));
        return result(0, r);
    }
}

static bool is_have(expr const & e) {
    return is_app(e) && is_have_annotation(app_fn(e)) && is_binding(get_annotation_arg(app_fn(e)));
}
static bool is_show(expr const & e) {
    return is_show_annotation(e) && is_app(get_annotation_arg(e)) &&
        is_lambda(app_fn(get_annotation_arg(e)));
}

auto pretty_fn::pp_have(expr const & e) -> result {
    expr proof   = app_arg(e);
    expr binding = get_annotation_arg(app_fn(e));
    auto p       = binding_body_fresh(binding, true);
    expr local   = p.second;
    expr body    = p.first;
    name const & n = local_pp_name(local);
    format type_fmt  = pp_child(local_type(local), 0).fmt();
    format proof_fmt = pp_child(proof, 0).fmt();
    format body_fmt  = pp_child(body, 0).fmt();
    format head_fmt  = *g_have_fmt;
    format r = head_fmt + space() + escape(n) + space();
    r += format(":") + nest(m_indent, line() + type_fmt + format(",") + space() + *g_from_fmt);
    r = group(r);
    r += nest(m_indent, line() + proof_fmt + format(","));
    r = group(r);
    r += line() + body_fmt;
    return result(0, r);
}

auto pretty_fn::pp_show(expr const & e) -> result {
    lean_assert(is_show(e));
    expr s           = get_annotation_arg(e);
    expr proof       = app_arg(s);
    expr type        = binding_domain(app_fn(s));
    format type_fmt  = pp_child(type, 0).fmt();
    format proof_fmt = pp_child(proof, 0).fmt();
    format r = *g_show_fmt + space() + nest(5, type_fmt) + format(",") + space() + *g_from_fmt;
    r = group(r);
    r += nest(m_indent, compose(line(), proof_fmt));
    return result(0, group(r));
}

auto pretty_fn::pp_explicit(expr const & e) -> result {
    result res_arg = pp_child(get_explicit_arg(e), max_bp());
    return result(max_bp(), compose(*g_explicit_fmt, res_arg.fmt()));
}

auto pretty_fn::pp_equation(expr const & e) -> format {
    lean_assert(is_equation(e));
    format r = format("|");
    buffer<expr> args;
    get_app_args(equation_lhs(e), args);
    for (expr const & arg : args) {
        r += space() + pp_child(arg, max_bp()).fmt();
    }
    r += space() + *g_assign_fmt + space() + pp_child(equation_rhs(e), 0).fmt();
    return r;
}

auto pretty_fn::pp_equations(expr const & e) -> optional<result> {
    buffer<expr> eqns;
    unsigned num_fns = equations_num_fns(e);
    to_equations(e, eqns);
    buffer<expr> fns;
    expr eqn = eqns[0];
    for (unsigned i = 0; i < num_fns; i++) {
        if (!is_lambda(eqn)) return optional<result>();
        if (has_loose_bvars(binding_domain(eqn))) return optional<result>();
        auto p = binding_body_fresh(eqn, true);
        fns.push_back(p.second);
        eqn = p.first;
    }
    format r;
    if (num_fns > 1) {
        r = format("mutual_def") + space();
        for (unsigned i = 0; i < num_fns; i++) {
            if (i > 0) r += format(", ");
            r += pp(fns[i]).fmt();
        }
        r += line();
    } else {
        r = format("def") + space() + pp(fns[0]).fmt() + space() + format(":") + space() + pp(local_type(fns[0])).fmt();
    }
    unsigned eqnidx = 0;
    for (unsigned fidx = 0; fidx < num_fns; fidx++) {
        if (num_fns > 1) {
            if (fidx > 0) r += line();
            r += format("with") + space() + pp(fns[fidx]).fmt() + space() + format(":") +
                space() + pp(local_type(fns[fidx])).fmt();
        }
        if (eqnidx >= eqns.size()) return optional<result>();
        expr eqn = eqns[eqnidx];
        while (is_lambda(eqn)) {
            eqn = binding_body_fresh(eqn, true).first;
        }
        eqnidx++;
        if (is_equation(eqn)) {
            r += line() + pp_equation(eqn);
            while (eqnidx < eqns.size()) {
                expr eqn = eqns[eqnidx];
                while (is_lambda(eqn)) {
                    eqn = binding_body_fresh(eqn, true).first;
                }
                if (is_equation(eqn) &&
                    get_app_fn(equation_lhs(eqn)) == fns[fidx]) {
                    r += line() + pp_equation(eqn);
                    eqnidx++;
                } else {
                    break;
                }
            }
        } else {
            /* noequation */
            r += line() + format("[none]");
        }
    }
    if (eqns.size() != eqnidx) return optional<result>();
    return optional<result>(r);
}

auto pretty_fn::pp_mdata(expr const & e) -> result {
    if (is_explicit(e)) {
        return pp_explicit(e);
    } else if (is_inaccessible(e)) {
        format r = format(".") + pp_child(get_annotation_arg(e), max_bp()).fmt();
        return result(r);
    } else if (is_annotation(e)) {
        if (m_annotations)
            return format("[") + format(get_annotation_kind(e)) + space() + pp(get_annotation_arg(e)).fmt() + format("]");
        else
            return pp(get_annotation_arg(e));
    } else if (is_as_pattern(e)) {
        auto lhs_fmt = pp_child(get_as_pattern_lhs(e), max_bp()).fmt();
        auto rhs_fmt = pp_child(get_as_pattern_rhs(e), max_bp()).fmt();
        return result(lhs_fmt + format("@") + rhs_fmt);
    } else if (is_equations(e)) {
        if (auto r = pp_equations(e))
            return *r;
        else
            return pp(mdata_expr(e));
    } else {
        return pp(mdata_expr(e));
    }
}

auto pretty_fn::pp_proj(expr const & e) -> result {
    format arg_fmt = pp_child(proj_expr(e), max_bp()).fmt();
    format idx_fmt(std::to_string(proj_idx(e).get_small_value() + 1));
    return result(arg_fmt + format(".") + idx_fmt);
    // return result(arg_fmt + format("[") + format(proj_sname(e)) + format("].") + idx_fmt);
}

auto pretty_fn::pp_let(expr e) -> result {
    buffer<std::tuple<expr, expr, expr>> decls;
    while (true) {
        expr t   = let_type(e);
        expr v   = let_value(e);
        expr b   = let_body(e);
        auto p   = let_body_fresh(e, true);
        decls.emplace_back(p.second, t, v);
        e        = p.first;
        if (!is_let(e))
            break;
    }
    lean_assert(!decls.empty());
    format r    = *g_let_fmt;
    unsigned sz = decls.size();
    for (unsigned i = 0; i < sz; i++) {
        expr l, t, v;
        std::tie(l, t, v) = decls[i];
        name const & n = local_pp_name(l);
        format beg     = i == 0 ? space() : line();
        format sep     = i < sz - 1 ? format(",") : format();
        format entry   = format(n);
        format v_fmt   = pp_child(v, 0).fmt();
        unsigned indent = m_compact_let ? 0 : m_indent;
        if (!m_binder_types || is_enf_neutral(t)) {
            entry += space() + *g_assign_fmt + nest(indent, line() + v_fmt + sep);
        } else {
            format t_fmt   = pp_child(t, 0).fmt();
            entry += space() + format(":") + space() + t_fmt + space() + *g_assign_fmt + nest(indent, line() + v_fmt + sep);
        }
        if (m_compact_let)
            r += nest(1, beg + group(entry));
        else
            r += nest(3 + 1, beg + group(entry));
    }
    format b = pp_child(e, 0).fmt();
    r += line() + *g_in_fmt + space() + nest(2 + 1, b);
    return result(0, r);
}

auto pretty_fn::pp_num(mpz const & n, unsigned bp) -> result {
    if (n.is_neg()) {
        auto prec = get_expr_precedence(m_token_table, "-");
        if (!prec || bp > *prec) {
            return result(paren(format(n.to_string())));
        }
    }
    return result(format(n.to_string()));
}

// Return the number of parameters in a notation declaration.
static unsigned get_num_parameters(notation_entry const & entry) {
    if (entry.is_numeral())
        return 0;
    unsigned r = 0;
    if (!entry.is_nud())
        r++;
    for (auto const & t : entry.get_transitions()) {
        switch (t.get_action().kind()) {
        case notation::action_kind::Skip:
        case notation::action_kind::Binder:
        case notation::action_kind::Binders:
            break;
        case notation::action_kind::Expr:
        case notation::action_kind::Exprs:
        case notation::action_kind::ScopedExpr:
        case notation::action_kind::Ext:
            r++;
        }
    }
    return r;
}

bool pretty_fn::match(level const & p, level const & l) {
    if (p == l)
        return true;
    if (m_universes)
        return false;
    if (is_placeholder(p))
        return true;
    if (is_succ(p) && is_succ(l))
        return match(succ_of(p), succ_of(l));
    return false;
}

bool pretty_fn::match(expr const & p, expr const & e, buffer<optional<expr>> & args) {
    if (get_pos(p)) {
        return match(unwrap_pos(p), e, args);
    } else if (is_explicit(p)) {
        return match(get_explicit_arg(p), e, args);
    } else if (is_as_atomic(p)) {
        return match(get_app_fn(get_as_atomic_arg(p)), e, args);
    } else if (is_bvar(p) && bvar_idx(p).is_small()) {
        unsigned vidx = bvar_idx(p).get_small_value();
        if (vidx >= args.size())
            return false;
        unsigned i = args.size() - vidx - 1;
        if (args[i])
            return *args[i] == e;
        args[i] = e;
        return true;
    } else if (is_placeholder(p)) {
        return true;
    } else if (is_constant(p) && is_constant(e)) {
        if (const_name(p) != const_name(e))
            return false;
        levels p_ls = const_levels(p);
        levels e_ls = const_levels(p);
        while (!is_nil(p_ls)) {
            if (is_nil(e_ls))
                return false; // e must have at least as many arguments as p
            if (!match(head(p_ls), head(e_ls)))
                return false;
            p_ls = tail(p_ls);
            e_ls = tail(e_ls);
        }
        return true;
    } else if (is_sort(p)) {
        if (!is_sort(e))
            return false;
        return match(sort_level(p), sort_level(e));
    } else if (is_app(e)) {
        buffer<expr> p_args, e_args;
        expr p_fn    = get_app_args(p, p_args);
        expr e_fn    = get_app_args(e, e_args);
        if (!match(p_fn, e_fn, args))
            return false;
        if (is_explicit(p)) {
            if (p_args.size() != e_args.size())
                return false;
            for (unsigned i = 0; i < p_args.size(); i++) {
                if (!match(p_args[i], e_args[i], args))
                    return false;
            }
            return true;
        } else {
            try {
                expr fn_type = m_ctx.infer(e_fn);
                unsigned j = 0;
                for (unsigned i = 0; i < e_args.size(); i++) {
                    fn_type = m_ctx.relaxed_whnf(fn_type);
                    if (!is_pi(fn_type))
                        return false;
                    expr const & body = binding_body(fn_type);
                    binder_info info  = binding_info(fn_type);
                    if (is_explicit(info)) {
                        if (j >= p_args.size())
                            return false;
                        if (!match(p_args[j], e_args[i], args))
                            return false;
                        j++;
                    }
                    fn_type = instantiate(body, e_args[i]);
                }
                return j == p_args.size();
            } catch (exception &) {
                return false;
            }
        }
    } else {
        return false;
    }
}

static unsigned get_some_precedence(token_table const & t, name const & tk) {
    if (tk.is_atomic() && tk.is_string()) {
        if (auto p = get_expr_precedence(t, tk.get_string().data())) // HACK: accessing Lean string as C String
            return *p;
    } else {
        if (auto p = get_expr_precedence(t, tk.to_string().c_str())) // HACK: accessing C++ string as C String
            return *p;
    }
    return 0;
}

auto pretty_fn::pp_notation_child(expr const & e, unsigned rbp, unsigned lbp) -> result {
    if (is_app(e)) {
        if (m_numerals) {
            if (auto n = to_num(e)) return pp_num(*n, lbp);
        }
        if (m_strings) {
            if (auto r = to_string(e)) return pp_string_literal(*r);
            if (auto r = to_char(m_ctx, e))   return pp_char_literal(*r);
        }
        expr const & f = app_fn(e);
        if (is_implicit(f)) {
            return pp_notation_child(f, rbp, lbp);
        } else if (!m_coercion && is_coercion(e)) {
            return pp_hide_coercion(e, rbp);
        } else if (!m_coercion && is_coercion_fn(e)) {
            return pp_hide_coercion_fn(e, rbp);
        }
    }
    result r = pp(e);
    /* see invariants of `pretty_fn::result`: Check that the surrounding notation would parse at least r
     * by the first invariant, and at most r (instead of the following token with binding power lbp) by the
     * second invariant. */
    if (rbp < r.lbp() && r.rbp() >= lbp) {
        return r;
    } else {
        return result(paren(r.fmt()));
    }
}

static bool is_atomic_notation(notation_entry const & entry) {
    if (!entry.is_nud())
        return false;
    list<notation::transition> const & ts = entry.get_transitions();
    if (!is_nil(tail(ts)))
        return false;
    return head(ts).get_action().kind() == notation::action_kind::Skip;
}

static format mk_tk_fmt(name const & tkn) {
    auto tk = tkn.to_string();
    if (!tk.empty() && tk.back() == ' ') {
        tk.pop_back();
        return format(tk) + line();
    } else {
        return format(tk);
    }
}

auto pretty_fn::pp_notation(notation_entry const & entry, buffer<optional<expr>> & args) -> optional<result> {
    if (entry.is_numeral()) {
        return some(result(format(entry.get_num().to_string())));
    } else if (is_atomic_notation(entry)) {
        format fmt   = format(head(entry.get_transitions()).get_token());
        return some(result(fmt));
    } else {
        using notation::transition;
        buffer<transition> ts;
        buffer<expr> locals; // from scoped_expr
        to_buffer(entry.get_transitions(), ts);
        format fmt;
        unsigned i         = ts.size();
        // bp of the last action
        unsigned last_rbp  = inf_bp()-1;
        // bp of the token immediately to the right of the action
        unsigned token_lbp = 0;
        bool last          = true;
        while (i > 0) {
            --i;
            format curr;
            notation::action const & a = ts[i].get_action();
            name const & tk = ts[i].get_token();
            format tk_fmt = mk_tk_fmt(ts[i].get_pp_token());
            switch (a.kind()) {
            case notation::action_kind::Skip:
                curr = tk_fmt;
                if (last)
                    // invariant fulfilled: Skip action will never parse a trailing token
                    last_rbp = inf_bp();
                break;
            case notation::action_kind::Expr:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    expr e = *args.back();
                    args.pop_back();
                    result e_r   = pp_notation_child(e, a.rbp(), token_lbp);
                    curr = tk_fmt + e_r.fmt();
                    if (last)
                        /* last_rbp can be no more than `a.rbp()`, since this is the bp used during parsing.
                         * However, `e_r.rbp()` may actually be smaller since it may be missing parentheses
                         * compared to the original input. For example, when re-printing `x >>= (fun y, z) = ...`,
                         * `e_r.fmt()` will be `fun y, z`. If we used the rbp of the `>>=` instead of
                         * `e_r.rbp()` (0), we would get the wrong output `x >>= fun y, z = ...`. */
                        last_rbp = std::min(a.rbp(), e_r.rbp());
                    break;
                }
            case notation::action_kind::Exprs:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    expr e = *args.back();
                    args.pop_back();
                    expr const & rec = a.get_rec();
                    optional<expr> const & ini = a.get_initial();
                    buffer<expr> rec_args;
                    bool matched_once = false;
                    while (true) {
                        args.resize(args.size() + 2);
                        if (!match(rec, e, args)) {
                            args.pop_back();
                            args.pop_back();
                            break;
                        }
                        optional<expr> new_e = args.back();
                        args.pop_back();
                        optional<expr> rec_arg = args.back();
                        args.pop_back();
                        if (!new_e || !rec_arg)
                            return optional<result>();
                        rec_args.push_back(*rec_arg);
                        e = *new_e;
                        matched_once = true;
                    }
                    if (!matched_once && ini)
                        return optional<result>();
                    if (ini) {
                        if (!match(*ini, e, args))
                            return optional<result>();
                    } else {
                        rec_args.push_back(e);
                    }
                    if (!a.is_fold_right())
                        std::reverse(rec_args.begin(), rec_args.end());
                    unsigned curr_lbp = token_lbp;
                    if (auto t = a.get_terminator()) {
                        curr = format(*t);
                        curr_lbp = get_some_precedence(m_token_table, *t);
                    }
                    unsigned j       = rec_args.size();
                    format sep_fmt   = format(a.get_sep());
                    unsigned sep_lbp = get_some_precedence(m_token_table, a.get_sep());
                    while (j > 0) {
                        --j;
                        result arg_res = pp_notation_child(rec_args[j], a.rbp(), curr_lbp);
                        if (j == 0) {
                            curr = tk_fmt + arg_res.fmt() + curr;
                        } else {
                            curr = sep_fmt + arg_res.fmt() + curr;
                        }
                        curr_lbp = sep_lbp;
                    }
                    break;
                }
            case notation::action_kind::Binder:
                if (locals.size() != 1)
                    return optional<result>();
                curr = tk_fmt + pp_binder(locals[0]);
                break;
            case notation::action_kind::Binders:
                curr = tk_fmt + pp_binders(locals);
                break;
            case notation::action_kind::ScopedExpr:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    expr e            = *args.back();
                    bool first_scoped = locals.empty();
                    unsigned i = 0;
                    args.pop_back();
                    expr const & rec = a.get_rec();
                    while (true) {
                        args.resize(args.size() + 1);
                        if (!match(rec, e, args) || !args.back()) {
                            args.pop_back();
                            break;
                        }
                        expr b = *args.back();
                        args.pop_back();
                        if (!((is_lambda(b) && a.use_lambda_abstraction()) ||
                              (is_pi(b) && !a.use_lambda_abstraction()))) {
                            break;
                        }
                        auto p = binding_body_fresh(b, true);
                        if (first_scoped) {
                            locals.push_back(p.second);
                        } else {
                            if (i >= locals.size() || locals[i] != p.second)
                                return optional<result>();
                        }
                        e = p.first;
                        i++;
                    }
                    if (locals.empty())
                        return optional<result>();
                    result e_r   = pp_notation_child(e, a.rbp(), token_lbp);
                    curr = tk_fmt + e_r.fmt();
                    if (last)
                        // see Expr action
                        last_rbp = std::min(a.rbp(), e_r.rbp());
                    break;
                }
            case notation::action_kind::Ext:
                return optional<result>();
            }
            token_lbp = get_some_precedence(m_token_table, tk);
            if (last) {
                fmt = curr;
                last = false;
            } else {
                fmt = curr + fmt;
            }
        }
        unsigned first_lbp = inf_bp();
        if (!entry.is_nud()) {
            first_lbp = token_lbp;
            lean_assert(!last);
            if (args.size() != 1 || !args.back())
                return optional<result>();
            expr e = *args.back();
            args.pop_back();
            format e_fmt = pp_notation_child(e, 0, token_lbp).fmt();
            fmt = e_fmt + fmt;
        }
        return optional<result>(result(first_lbp, last_rbp, group(nest(m_indent, fmt))));
    }
}

auto pretty_fn::pp_notation(expr const & e) -> optional<result> {
    if (!m_notation || is_var(e))
        return optional<result>();
    for (notation_entry const & entry : get_notation_entries(m_env, head_index(e))) {
        if (entry.group() == notation_entry_group::Reserve)
            continue;
        if (!m_unicode && !entry.is_safe_ascii())
            continue; // ignore this notation declaration since unicode support is not enabled
        unsigned num_params = get_num_parameters(entry);
        buffer<optional<expr>> args;
        args.resize(num_params);
        if (match(entry.get_expr(), e, args)) {
            if (auto r = pp_notation(entry, args))
                return r;
        }
    }
    return optional<result>();
}

static bool is_pp_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::App:
    case expr_kind::Lambda:
    case expr_kind::Pi:
        return false;
    default:
        return true;
    }
}

static bool is_subtype(expr const & e) {
    return
        is_constant(get_app_fn(e), get_subtype_name()) &&
        get_app_num_args(e) == 2 &&
        is_lambda(app_arg(e));
}

auto pretty_fn::pp_subtype(expr const & e) -> result {
    lean_assert(is_subtype(e));
    expr pred = app_arg(e);
    lean_assert(is_lambda(pred));
    auto p     = binding_body_fresh(pred, true);
    expr body  = p.first;
    expr local = p.second;
    format r   = bracket("{", format(local_pp_name(local)) + space() + format("//") + space() + pp_child(body, 0).fmt(), "}");
    return result(r);
}

static bool is_emptyc(expr const & e) {
    return
        is_constant(get_app_fn(e), get_has_emptyc_emptyc_name()) &&
        get_app_num_args(e) == 2;
}

static bool is_singleton(expr const & e) {
    return
        is_constant(get_app_fn(e), get_singleton_name()) &&
        get_app_num_args(e) == 5;
}

static bool is_insert(expr const & e) {
    return
        is_constant(get_app_fn(e), get_has_insert_insert_name()) &&
        get_app_num_args(e) == 5;
}

/* Return true iff 'e' encodes a nonempty finite collection,
   and stores its elements at elems. */
static bool is_explicit_collection(expr const & e, buffer<expr> & elems) {
    if (is_emptyc(e)) {
        return true;
    } else if (is_singleton(e)) {
        elems.push_back(app_arg(e));
        return true;
    } else if (is_insert(e) && is_explicit_collection(app_arg(e), elems)) {
        elems.push_back(app_arg(app_fn(e)));
        return true;
    } else {
        return false;
    }
}

auto pretty_fn::pp_explicit_collection(buffer<expr> const & elems) -> result {
    if (elems.empty()) {
        return result(format(m_unicode ? "∅" : "{}"));
    } else {
        format r = pp_child(elems[0], 0).fmt();
        for (unsigned i = 1; i < elems.size(); i++) {
            r += nest(m_indent, format(",") + line() + pp_child(elems[i], 0).fmt());
        }
        r = group(bracket("{", r, "}"));
        return result(r);
    }
}

bool is_set_of(expr const & e) {
    return
        is_constant(get_app_fn(e), get_set_of_name()) &&
        get_app_num_args(e) == 2 &&
        is_lambda(app_arg(e));
}

auto pretty_fn::pp_set_of(expr const & e) -> result {
    lean_assert(is_set_of(e));
    expr pred = app_arg(e);
    lean_assert(is_lambda(pred));
    auto p     = binding_body_fresh(pred, true);
    expr body  = p.first;
    expr local = p.second;
    format r   = bracket("{",
                         pp_binder(local) + space() + format("|") + space() +
                         pp_child(body, 0).fmt(), "}");
    return result(r);
}

static bool is_sep(expr const & e) {
    return
        is_constant(get_app_fn(e), get_has_sep_sep_name()) &&
        get_app_num_args(e) == 5 &&
        is_lambda(app_arg(app_fn(e)));
}

auto pretty_fn::pp_sep(expr const & e) -> result {
    lean_assert(is_sep(e));
    expr s    = app_arg(e);
    expr pred = app_arg(app_fn(e));
    lean_assert(is_lambda(pred));
    auto p     = binding_body_fresh(pred, true);
    expr body  = p.first;
    expr local = p.second;
    format in  = format(m_unicode ? "∈" : "in");
    format r   = bracket("{",
                         format(local_pp_name(local)) + space() + in + space() +
                         pp_child(s, 0).fmt() + space() + format("|") + space() +
                         pp_child(body, 0).fmt(), "}");
    return result(r);
}

auto pretty_fn::pp_prod(expr const & e) -> result {
    format r = pp(app_arg(app_fn(e))).fmt();
    auto it = app_arg(e);
    while (is_app_of(it, get_prod_mk_name(), 4)) {
        r += format(",") + line();
        r += pp(app_arg(app_fn(it))).fmt();
        it = app_arg(it);
    }
    r += format(",") + line();
    r += pp(it).fmt();
    return result(paren(group(r)));
}

auto pretty_fn::pp_lit(expr const & e) -> result {
    switch (lit_value(e).kind()) {
    case literal_kind::Nat:
        return pp_num(lit_value(e).get_nat().to_mpz(), 0);
    case literal_kind::String:
        return pp_string_literal(lit_value(e).get_string().to_std_string());
    }
    lean_unreachable();
}

auto pretty_fn::pp(expr const & e, bool ignore_hide) -> result {
    check_system("pretty printer");
    if ((m_depth >= m_max_depth ||
         m_num_steps > m_max_steps ||
         (m_hide_full_terms && !ignore_hide && !has_expr_metavar(e))) &&
        !is_pp_atomic(e)) {
        return result(m_unicode ? *g_ellipsis_n_fmt : *g_ellipsis_fmt);
    }
    flet<unsigned> let_d(m_depth, m_depth+1);
    m_num_steps++;

    if (m_numerals) {
        if (auto n = to_num(e)) return pp_num(*n, 0);
    }
    if (m_strings) {
        if (auto r = to_string(e))      return pp_string_literal(*r);
        if (auto r = to_char(m_ctx, e)) return pp_char_literal(*r);
    }
    try {
        if (!m_proofs && !is_constant(e) && !is_mlocal(e) && !has_loose_bvars(e) && is_prop(m_ctx.infer(e))) {
            return result(format("_"));
        }
    } catch (exception) {}

    if (auto r = pp_notation(e))
        return *r;

    if (m_notation) {
        if (is_subtype(e))
            return pp_subtype(e);
        if (is_sep(e))
            return pp_sep(e);
        if (is_set_of(e))
            return pp_set_of(e);
        buffer<expr> elems;
        if (is_explicit_collection(e, elems))
            return pp_explicit_collection(elems);
        if (is_app_of(e, get_prod_mk_name(), 4))
            return pp_prod(e);
    }

    if (is_placeholder(e))  return result(*g_placeholder_fmt);
    if (is_show(e))         return pp_show(e);
    if (is_have(e))         return pp_have(e);
    if (is_typed_expr(e))   return pp(get_typed_expr_expr(e));
    if (m_num_nat_coe)
        if (auto k = to_unsigned(e))
            return format(*k);
    switch (e.kind()) {
    case expr_kind::BVar:      return pp_var(e);
    case expr_kind::FVar:      return pp_fvar(e);
    case expr_kind::Local:     return pp_local(e);
    case expr_kind::Sort:      return pp_sort(e);
    case expr_kind::MData:     return pp_mdata(e);
    case expr_kind::Proj:      return pp_proj(e);
    case expr_kind::Const:     return pp_const(e);
    case expr_kind::MVar:      return pp_meta(e);
    case expr_kind::App:       return pp_app(e);
    case expr_kind::Lambda:    return pp_lambda(e);
    case expr_kind::Pi:        return pp_pi(e);
    case expr_kind::Let:       return pp_let(e);
    case expr_kind::Lit:       return pp_lit(e);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

pretty_fn::pretty_fn(environment const & env, options const & o, abstract_type_context & ctx):
    m_env(env), m_ctx(ctx), m_token_table(get_token_table(env)) {
    set_options_core(o);
    m_meta_prefix   = "M";
    m_next_meta_idx = 1;
}

// Custom beta reduction procedure for the pretty printer.
// We don't want to reduce application in show annotations.
class pp_beta_reduce_fn : public replace_visitor {
    virtual expr visit_meta(expr const & e) override { return e; }
    virtual expr visit_local(expr const & e) override { return e; }
    virtual expr visit_fvar(expr const & e) override { return e; }

    virtual expr visit_mdata(expr const & e) override {
        if (is_show_annotation(e) && is_app(get_annotation_arg(e))) {
            expr const & n = get_annotation_arg(e);
            expr new_fn  = visit(app_fn(n));
            expr new_arg = visit(app_arg(n));
            return mk_show_annotation(mk_app(new_fn, new_arg));
        } else {
            return replace_visitor::visit_mdata(e);
        }
    }

    virtual expr visit_app(expr const & e) override {
        expr new_e = replace_visitor::visit_app(e);
        if (is_head_beta(new_e))
            return visit(head_beta_reduce(new_e));
        else
            return new_e;
    }
};

// check whether a space must be inserted between the strings so that lexing them would
// produce separate tokens
std::pair<bool, token_table const *> pretty_fn::needs_space_sep(token_table const * last, std::string const & s1, std::string const & s2) const {
    if (s1.empty() || (is_id_rest(get_utf8_last_char(s1.data()), s1.data() + s1.size()) && is_id_rest(s2.data(), s2.data() + s2.size())))
        return mk_pair(true, nullptr); // would be lexed as a single identifier without space

    if (last) {
        // complete deferred two-token lookahead
        for (char c : s2) {
            last = last->find(c);
            if (!last)
                break;
            if (last->value())
                return mk_pair(true, nullptr);
        }
        if (last) {
            // would need an even larger lookahead, give up
            return mk_pair(true, nullptr);
        }
    }

    // check whether s1 + s2 has a longer prefix in the token table than s1
    token_table const * t = &m_token_table;
    for (char c : s1) {
        t = t->find(c);
        if (!t)
            return mk_pair(false, nullptr); // s1 must be an identifier, and we know s2 does not start with is_id_rest
    }
    for (char c : s2) {
        t = t->find(c);
        if (!t)
            return mk_pair(false, nullptr);
        if (t->value())
            return mk_pair(true, nullptr);
    }

    // the next identifier may expand s1 + s2 to a token, defer decision
    return mk_pair(false, t);
}

format pretty_fn::operator()(expr const & e) {
    auto purified = purify(m_beta ? pp_beta_reduce_fn()(e) : e);

    if (!m_options.contains(get_pp_proofs_name()) && !get_pp_all(m_options)) {
        try {
            m_proofs = has_loose_bvars(purified) || is_prop(m_ctx.infer(purified));
        } catch (exception) {
            m_proofs = true;
        }
    }

    m_depth = 0; m_num_steps = 0;
    result r = pp_child(purified, 0);

    return r.fmt();
}

formatter_factory mk_pretty_formatter_factory() {
    return [](environment const & env, options const & o, abstract_type_context & ctx) { // NOLINT
        auto fn_ptr = std::make_shared<pretty_fn>(env, o, ctx);
        return formatter(o, [=](expr const & e, options const & new_o) {
                fn_ptr->set_options(new_o);
                return (*fn_ptr)(e);
            });
    };
}

format pp(environment const & env, metavar_context const & mctx, local_context const & lctx, options const & opts, expr const & e) {
    type_context_old ctx(env, opts, mctx, lctx, transparency_mode::All);
    return pretty_fn(env, opts, ctx)(e);
}

extern "C" object * lean_pp_expr(object * env, object * mctx, object * lctx, object * opts, object * e) {
    return pp(environment(env), metavar_context(mctx), local_context(lctx), options(opts), expr(e)).steal();
}
}
