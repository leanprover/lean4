/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "util/flet.h"
#include "kernel/replace_fn.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/annotation.h"
#include "library/aliases.h"
#include "library/scoped_ext.h"
#include "library/coercion.h"
#include "library/expr_pair.h"
#include "library/placeholder.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/explicit.h"
#include "library/typed_expr.h"
#include "library/num.h"
#include "library/util.h"
#include "library/let.h"
#include "library/print.h"
#include "library/abbreviation.h"
#include "library/pp_options.h"
#include "library/constants.h"
#include "library/replace_visitor.h"
#include "library/definitional/equations.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/util.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/local_ref_info.h"

namespace lean {
static format * g_ellipsis_n_fmt  = nullptr;
static format * g_ellipsis_fmt    = nullptr;
static format * g_placeholder_fmt = nullptr;
static format * g_lambda_n_fmt    = nullptr;
static format * g_lambda_fmt      = nullptr;
static format * g_forall_n_fmt    = nullptr;
static format * g_forall_fmt      = nullptr;
static format * g_pi_n_fmt        = nullptr;
static format * g_pi_fmt          = nullptr;
static format * g_arrow_n_fmt     = nullptr;
static format * g_arrow_fmt       = nullptr;
static format * g_let_fmt         = nullptr;
static format * g_in_fmt          = nullptr;
static format * g_assign_fmt      = nullptr;
static format * g_have_fmt        = nullptr;
static format * g_assert_fmt      = nullptr;
static format * g_from_fmt        = nullptr;
static format * g_visible_fmt     = nullptr;
static format * g_show_fmt        = nullptr;
static format * g_explicit_fmt    = nullptr;
static name   * g_tmp_prefix      = nullptr;

class nat_numeral_pp {
    expr m_num_type;
    name m_nat;
    expr m_nat_of_num;
    expr m_zero;
    expr m_succ;
public:
    nat_numeral_pp():
        m_num_type(mk_constant(get_num_name())),
        m_nat(get_nat_name()),
        m_nat_of_num(mk_constant(get_nat_of_num_name())),
        m_zero(mk_constant(get_nat_zero_name())),
        m_succ(mk_constant(get_nat_succ_name())) {
    }

    // Return ture if the environment has a coercion from num->nat
    bool has_coercion_num_nat(environment const & env) const {
        list<expr> coes = get_coercions(env, m_num_type, m_nat);
        if (length(coes) != 1)
            return false;
        return head(coes) == m_nat_of_num;
    }

    // Return an unsigned if \c e if of the form (succ^k zero), and k
    // fits in a machine unsigned integer.
    optional<unsigned> to_unsigned(expr const & e) const {
        unsigned r = 0;
        expr const * it = &e;
        while (true) {
            if (*it == m_zero) {
                return optional<unsigned>(r);
            } else if (is_app(*it) && app_fn(*it) == m_succ) {
                if (r == std::numeric_limits<unsigned>::max())
                    return optional<unsigned>(); // just in case, it does not really happen in practice
                r++;
                it = &app_arg(*it);
            } else {
                return optional<unsigned>();
            }
        }
    }
};

static nat_numeral_pp * g_nat_numeral_pp = nullptr;

static bool has_coercion_num_nat(environment const & env) {
    return g_nat_numeral_pp->has_coercion_num_nat(env);
}

static optional<unsigned> to_unsigned(expr const & e) {
    return g_nat_numeral_pp->to_unsigned(e);
}

void initialize_pp() {
    g_ellipsis_n_fmt  = new format(highlight(format("\u2026")));
    g_ellipsis_fmt    = new format(highlight(format("...")));
    g_placeholder_fmt = new format(highlight(format("_")));
    g_lambda_n_fmt    = new format(highlight_keyword(format("\u03BB")));
    g_lambda_fmt      = new format(highlight_keyword(format("fun")));
    g_forall_n_fmt    = new format(highlight_keyword(format("\u2200")));
    g_forall_fmt      = new format(highlight_keyword(format("forall")));
    g_pi_n_fmt        = new format(highlight_keyword(format("Π")));
    g_pi_fmt          = new format(highlight_keyword(format("Pi")));
    g_arrow_n_fmt     = new format(highlight_keyword(format("\u2192")));
    g_arrow_fmt       = new format(highlight_keyword(format("->")));
    g_let_fmt         = new format(highlight_keyword(format("let")));
    g_in_fmt          = new format(highlight_keyword(format("in")));
    g_assign_fmt      = new format(highlight_keyword(format(":=")));
    g_have_fmt        = new format(highlight_keyword(format("have")));
    g_assert_fmt      = new format(highlight_keyword(format("assert")));
    g_from_fmt        = new format(highlight_keyword(format("from")));
    g_visible_fmt     = new format(highlight_keyword(format("[visible]")));
    g_show_fmt        = new format(highlight_keyword(format("show")));
    g_explicit_fmt    = new format(highlight_keyword(format("@")));
    g_tmp_prefix      = new name(name::mk_internal_unique_name());
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
    delete g_pi_n_fmt;
    delete g_pi_fmt;
    delete g_arrow_n_fmt;
    delete g_arrow_fmt;
    delete g_let_fmt;
    delete g_in_fmt;
    delete g_assign_fmt;
    delete g_have_fmt;
    delete g_assert_fmt;
    delete g_from_fmt;
    delete g_visible_fmt;
    delete g_show_fmt;
    delete g_explicit_fmt;
    delete g_tmp_prefix;
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

name pretty_fn::mk_metavar_name(name const & m) {
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
        name new_m = m_meta_prefix.append_after(m_next_meta_idx);
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
    if (!m_universes || !m_purify_metavars || !has_meta(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l))
                return some_level(l);
            if (is_meta(l))
                return some_level(mk_meta_univ(mk_metavar_name(meta_id(l))));
            return none_level();
        });
}

/** \brief Make sure that all metavariables have reasonable names,
    and for all local constants l1 l2, local_pp_name(l1) != local_pp_name(l2).

    \remark pretty_fn will create new local constants when pretty printing,
    but it will make sure that the new constants will not produce collisions.
*/
expr pretty_fn::purify(expr const & e) {
    if (!has_expr_metavar(e) && !has_local(e) && (!m_universes || !has_univ_metavar(e)))
        return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_local(e) && (!m_universes || !has_univ_metavar(e)))
                return some_expr(e);
            else if (is_metavar(e) && m_purify_metavars)
                return some_expr(mk_metavar(mk_metavar_name(mlocal_name(e)), mlocal_type(e)));
            else if (is_local(e))
                return some_expr(mk_local(mlocal_name(e), mk_local_name(mlocal_name(e), local_pp_name(e)), mlocal_type(e), local_info(e)));
            else if (is_constant(e))
                return some_expr(update_constant(e, map(const_levels(e), [&](level const & l) { return purify(l); })));
            else if (is_sort(e))
                return some_expr(update_sort(e, purify(sort_level(e))));
            else
                return none_expr();
        });
}

void pretty_fn::set_options_core(options const & o) {
    m_options         = o;
    m_indent          = get_pp_indent(o);
    m_max_depth       = get_pp_max_depth(o);
    m_max_steps       = get_pp_max_steps(o);
    m_implict         = get_pp_implicit(o);
    m_unicode         = get_pp_unicode(o);
    m_coercion        = get_pp_coercions(o);
    m_notation        = get_pp_notation(o);
    m_universes       = get_pp_universes(o);
    m_full_names      = get_pp_full_names(o);
    m_private_names   = get_pp_private_names(o);
    m_metavar_args    = get_pp_metavar_args(o);
    m_purify_metavars = get_pp_purify_metavars(o);
    m_purify_locals   = get_pp_purify_locals(o);
    m_beta            = get_pp_beta(o);
    m_numerals        = get_pp_numerals(o);
    m_abbreviations   = get_pp_abbreviations(o);
    m_extra_spaces    = get_pp_extra_spaces(o);
    m_preterm         = get_pp_preterm(o);
    m_hide_full_terms = get_formatter_hide_full_terms(o);
    m_num_nat_coe     = m_numerals && !m_coercion && has_coercion_num_nat(m_env);
}

void pretty_fn::set_options(options const & o) {
    if (is_eqp(o, m_options))
        return;
    set_options_core(o);
}

format pretty_fn::pp_level(level const & l) {
    return ::lean::pp(l, m_unicode, m_indent);
}

bool pretty_fn::is_implicit(expr const & f) {
    // Remark: we assume preterms do not have implicit arguments,
    // since they have not been elaborated yet.
    // Moreover, the type checker will probably produce an error
    // when trying to infer type information
    if (m_implict || m_preterm)
        return false; // showing implicit arguments
    if (!closed(f)) {
        // the Lean type checker assumes expressions are closed.
        return false;
    }
    try {
        binder_info bi = binding_info(m_tc.ensure_pi(m_tc.infer(f).first).first);
        return bi.is_implicit() || bi.is_strict_implicit() || bi.is_inst_implicit();
    } catch (exception &) {
        return false;
    }
}

bool pretty_fn::is_prop(expr const & e) {
    try {
        return m_env.impredicative() && m_tc.is_prop(e).first;
    } catch (exception &) {
        return false;
    }
}

auto pretty_fn::pp_coercion_fn(expr const & e, unsigned sz, bool ignore_hide) -> result {
    if (sz == 1) {
        return pp_child(app_arg(e), max_bp()-1, ignore_hide);
    } else if (is_app(e) && is_implicit(app_fn(e))) {
        return pp_coercion_fn(app_fn(e), sz-1, ignore_hide);
    } else {
        expr const & fn = app_fn(e);
        result res_fn   = pp_coercion_fn(fn, sz-1, ignore_hide);
        format fn_fmt   = res_fn.fmt();
        if (m_implict && sz == 2 && has_implicit_args(fn))
            fn_fmt = compose(*g_explicit_fmt, fn_fmt);
        result res_arg  = pp_child(app_arg(e), max_bp(), ignore_hide);
        return result(max_bp()-1, group(compose(fn_fmt, nest(m_indent, compose(line(), res_arg.fmt())))));
    }
}

auto pretty_fn::pp_coercion(expr const & e, unsigned bp, bool ignore_hide) -> result {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    optional<pair<name, unsigned>> r = is_coercion(m_env, f);
    lean_assert(r);
    if (r->second >= args.size()) {
        return pp_child_core(e, bp, ignore_hide);
    } else if (r->second == args.size() - 1) {
        return pp_child(args.back(), bp, ignore_hide);
    } else {
        unsigned sz = args.size() - r->second;
        lean_assert(sz >= 2);
        auto r = pp_coercion_fn(e, sz, ignore_hide);
        if (r.rbp() < bp) {
            return result(paren(r.fmt()));
        } else {
            return r;
        }
    }
}

auto pretty_fn::pp_child_core(expr const & e, unsigned bp, bool ignore_hide) -> result {
    result r = pp(e, ignore_hide);
    if (r.rbp() < bp) {
        return result(paren(r.fmt()));
    } else {
        return r;
    }
}

// Return some result if \c e is of the form (c p_1 ... p_n) where
// c is a constant, and p_i's are parameters fixed in a section.
auto pretty_fn::pp_local_ref(expr const & e) -> optional<result> {
    lean_assert(is_app(e));
    expr const & rfn = get_app_fn(e);
    if (is_constant(rfn)) {
        if (auto info = get_local_ref_info(m_env, const_name(rfn))) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() == info->second) {
                // TODO(Leo): must check if the arguments are really the fixed parameters.
                return some(pp_const(rfn));
            }
        }
    }
    return optional<result>();
}

auto pretty_fn::pp_child(expr const & e, unsigned bp, bool ignore_hide) -> result {
    if (auto it = is_abbreviated(e))
        return pp_abbreviation(e, *it, false, bp, ignore_hide);
    if (is_app(e)) {
        if (auto r = pp_local_ref(e))
            return *r;
        expr const & f = app_fn(e);
        if (auto it = is_abbreviated(f)) {
            return pp_abbreviation(e, *it, true, bp, ignore_hide);
        } else if (is_implicit(f)) {
            return pp_child(f, bp, ignore_hide);
        } else if (!m_coercion && is_coercion(m_env, f)) {
            return pp_coercion(e, bp, ignore_hide);
        }
    }
    return pp_child_core(e, bp, ignore_hide);
}

auto pretty_fn::pp_var(expr const & e) -> result {
    unsigned vidx = var_idx(e);
    return result(compose(format("#"), format(vidx)));
}

auto pretty_fn::pp_sort(expr const & e) -> result {
    if (m_env.impredicative() && e == mk_Prop()) {
        return result(format("Prop"));
    } else if (m_universes) {
        return result(group(format("Type.{") + nest(6, pp_level(sort_level(e))) + format("}")));
    } else {
        return result(format("Type"));
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

optional<name> pretty_fn::is_abbreviated(expr const & e) const {
    if (m_abbreviations)
        return ::lean::is_abbreviated(m_env, e);
    return optional<name>();
}

auto pretty_fn::pp_const(expr const & e) -> result {
    name n = const_name(e);
    if (!m_full_names) {
        if (auto it = is_aliased(n)) {
            if (!m_private_names || !hidden_to_user_name(m_env, n))
                n = *it;
        } else {
            for (name const & ns : get_namespaces(m_env)) {
                if (!ns.is_anonymous()) {
                    name new_n = n.replace_prefix(ns, name());
                    if (new_n != n &&
                        !new_n.is_anonymous() &&
                        (!new_n.is_atomic() || !is_protected(m_env, n))) {
                        n = new_n;
                        break;
                    }
                }
            }
        }
    }
    if (!m_private_names) {
        if (auto n1 = hidden_to_user_name(m_env, n))
            n = *n1;
    }
    if (m_universes && !empty(const_levels(e))) {
        unsigned first_idx = 0;
        buffer<level> ls;
        to_buffer(const_levels(e), ls);
        if (auto info = get_local_ref_info(m_env, n)) {
            if (ls.size() <= info->first)
                return result(format(n));
            else
                first_idx = info->first;
        }
        format r = compose(format(n), format(".{"));
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
        return result(format(n));
    }
}

auto pretty_fn::pp_meta(expr const & e) -> result {
    if (m_purify_metavars)
        return result(compose(format("?"), format(mlocal_name(e))));
    else
        return result(compose(format("?M."), format(mlocal_name(e))));
}

auto pretty_fn::pp_local(expr const & e) -> result {
    return result(format(local_pp_name(e)));
}

bool pretty_fn::has_implicit_args(expr const & f) {
    if (!closed(f) || m_preterm) {
        // The Lean type checker assumes expressions are closed.
        // If preterms are being processed, then we assume
        // there are no implicit arguments.
        return false;
    }
    name_generator ngen(*g_tmp_prefix);
    try {
        expr type = m_tc.whnf(m_tc.infer(f).first).first;
        while (is_pi(type)) {
            binder_info bi = binding_info(type);
            if (bi.is_implicit() || bi.is_strict_implicit() || bi.is_inst_implicit())
                return true;
            expr local = mk_local(ngen.next(), binding_name(type), binding_domain(type), binding_info(type));
            type = m_tc.whnf(instantiate(binding_body(type), local)).first;
        }
        return false;
    } catch (exception &) {
        return false;
    }
}

auto pretty_fn::pp_app(expr const & e) -> result {
    if (auto r = pp_local_ref(e))
        return *r;
    expr const & fn = app_fn(e);
    if (auto it = is_abbreviated(fn))
        return pp_abbreviation(e, *it, true);
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

format pretty_fn::pp_binder_block(buffer<name> const & names, expr const & type, binder_info const & bi) {
    format r;
    r += format(open_binder_string(bi, m_unicode));
    for (name const & n : names) {
        r += format(n);
        r += space();
    }
    r += compose(colon(), nest(m_indent, compose(line(), pp_child(type, 0).fmt())));
    r += format(close_binder_string(bi, m_unicode));
    return group(r);
}

format pretty_fn::pp_binders(buffer<expr> const & locals) {
    unsigned num     = locals.size();
    buffer<name> names;
    expr local       = locals[0];
    expr   type      = mlocal_type(local);
    binder_info bi   = local_info(local);
    names.push_back(local_pp_name(local));
    format r;
    for (unsigned i = 1; i < num; i++) {
        expr local = locals[i];
        if (mlocal_type(local) == type && local_info(local) == bi) {
            names.push_back(local_pp_name(local));
        } else {
            r += group(compose(line(), pp_binder_block(names, type, bi)));
            names.clear();
            type = mlocal_type(local);
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
    r += compose(comma(), nest(m_indent, compose(line(), pp_child(b, 0).fmt())));
    return result(0, r);
}

/** \brief Similar to #is_arrow, but only returns true if binder_info is the default one.
    That is, we don't want to lose binder info when pretty printing.
*/
static bool is_default_arrow(expr const & e) {
    return is_arrow(e) && binding_info(e) == binder_info();
}

auto pretty_fn::pp_pi(expr const & e) -> result {
    if (is_default_arrow(e)) {
        result lhs = pp_child(binding_domain(e), get_arrow_prec());
        result rhs = pp_child(lift_free_vars(binding_body(e), 1), get_arrow_prec()-1);
        format r   = group(lhs.fmt() + space() + (m_unicode ? *g_arrow_n_fmt : *g_arrow_fmt) + line() + rhs.fmt());
        return result(get_arrow_prec()-1, r);
    } else {
        expr b = e;
        buffer<expr> locals;
        while (is_pi(b) && !is_default_arrow(b)) {
            auto p = binding_body_fresh(b, true);
            locals.push_back(p.second);
            b = p.first;
        }
        format r;
        if (is_prop(b))
            r = m_unicode ? *g_forall_n_fmt : *g_forall_fmt;
        else
            r = m_unicode ? *g_pi_n_fmt : *g_pi_fmt;
        r += pp_binders(locals);
        r += compose(comma(), nest(m_indent, compose(line(), pp_child(b, 0).fmt())));
        return result(0, r);
    }
}

static bool is_have(expr const & e) { return is_app(e) && is_have_annotation(app_fn(e)); }
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
    format type_fmt  = pp_child(mlocal_type(local), 0).fmt();
    format proof_fmt = pp_child(proof, 0).fmt();
    format body_fmt  = pp_child(body, 0).fmt();
    format head_fmt  = (binding_info(binding).is_contextual()) ? *g_assert_fmt : *g_have_fmt;
    format r = head_fmt + space() + format(n) + space();
    r += colon() + nest(m_indent, line() + type_fmt + comma() + space() + *g_from_fmt);
    r = group(r);
    r += nest(m_indent, line() + proof_fmt + comma());
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
    format r = *g_show_fmt + space() + nest(5, type_fmt) + comma() + space() + *g_from_fmt;
    r = group(r);
    r += nest(m_indent, compose(line(), proof_fmt));
    return result(0, group(r));
}

auto pretty_fn::pp_explicit(expr const & e) -> result {
    result res_arg = pp_child(get_explicit_arg(e), max_bp());
    return result(max_bp(), compose(*g_explicit_fmt, res_arg.fmt()));
}

auto pretty_fn::pp_macro(expr const & e) -> result {
    if (is_explicit(e)) {
        return pp_explicit(e);
    } else if (is_inaccessible(e)) {
        format li = m_unicode ? format("⌞") : format("?(");
        format ri = m_unicode ? format("⌟") : format(")");
        return result(group(nest(1, li + pp(get_annotation_arg(e)).fmt() + ri)));
    } else if (is_annotation(e)) {
        return pp(get_annotation_arg(e));
    } else {
        // TODO(Leo): have macro annotations
        // fix macro<->pp interface
        format r = compose(format("["), format(macro_def(e).get_name()));
        for (unsigned i = 0; i < macro_num_args(e); i++)
            r += nest(m_indent, compose(line(), pp_child(macro_arg(e, i), max_bp()).fmt()));
        r += format("]");
        return result(group(r));
    }
}

auto pretty_fn::pp_let(expr e) -> result {
    buffer<pair<name, expr>> decls;
    while (true) {
        if (!is_let(e))
            break;
        name n   = get_let_var_name(e);
        expr v   = get_let_value(e);
        expr b   = get_let_body(e);
        lean_assert(closed(b));
        expr b1  = abstract(b, v);
        if (closed(b1)) {
            e = b1;
        } else {
            n = pick_unused_name(b1, n);
            decls.emplace_back(n, v);
            e = instantiate(b1, mk_constant(n));
        }
    }
    if (decls.empty())
        return pp(e);
    format r    = *g_let_fmt;
    unsigned sz = decls.size();
    for (unsigned i = 0; i < sz; i++) {
        name const & n = decls[i].first;
        expr const & v = decls[i].second;
        format beg     = i == 0 ? space() : line();
        format sep     = i < sz - 1 ? comma() : format();
        format entry   = format(n);
        format v_fmt   = pp_child(v, 0).fmt();
        entry += space() + *g_assign_fmt + nest(m_indent, line() + v_fmt + sep);
        r += nest(3 + 1, beg + group(entry));
    }
    format b = pp_child(e, 0).fmt();
    r += line() + *g_in_fmt + space() + nest(2 + 1, b);
    return result(0, r);
}

auto pretty_fn::pp_num(mpz const & n) -> result {
    return result(format(n));
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
        case notation::action_kind::LuaExt:
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
    if (is_explicit(p)) {
        return match(get_explicit_arg(p), e, args);
    } else if (is_var(p)) {
        unsigned vidx = var_idx(p);
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
        bool consume = is_consume_args(p_fn);
        if (consume)
            p_fn     = get_consume_args_arg(p_fn);
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
                expr fn_type = m_tc.infer(e_fn).first;
                unsigned j = 0;
                for (unsigned i = 0; i < e_args.size(); i++) {
                    fn_type                  = m_tc.ensure_pi(fn_type).first;
                    expr const & body        = binding_body(fn_type);
                    binder_info const & info = binding_info(fn_type);
                    if ((!consume || closed(body)) && is_explicit(info)) {
                        if (j >= p_args.size())
                            return false;
                        if (!match(p_args[j], e_args[i], args))
                            return false;
                        j++;
                    }
                    fn_type = instantiate(body, e_args[i]);
                }
                return j == p_args.size();
            } catch (exception&) {
                return false;
            }
        }
    } else {
        return false;
    }
}

static unsigned get_some_precedence(token_table const & t, name const & tk) {
    if (tk.is_atomic() && tk.is_string()) {
        if (auto p = get_expr_precedence(t, tk.get_string()))
            return *p;
    } else {
        if (auto p = get_expr_precedence(t, tk.to_string().c_str()))
            return *p;
    }
    return 0;
}

auto pretty_fn::pp_notation_child(expr const & e, unsigned lbp, unsigned rbp) -> result {
    if (auto it = is_abbreviated(e))
        return pp_abbreviation(e, *it, false, rbp);
    if (is_app(e)) {
        expr const & f = app_fn(e);
        if (auto it = is_abbreviated(f)) {
            return pp_abbreviation(e, *it, true, rbp);
        } else if (is_implicit(f)) {
            return pp_notation_child(f, lbp, rbp);
        } else if (!m_coercion && is_coercion(m_env, f)) {
            return pp_coercion(e, rbp);
        }
    }
    result r = pp(e);
    if (r.rbp() < lbp || r.lbp() <= rbp) {
        return result(paren(r.fmt()));
    } else {
        return r;
    }
}

static bool add_extra_space_first(name const & tk) {
    // TODO(Leo): this is a hard-coded temporary solution for deciding whether extra
    // spaces should be added or not when pretty printing notation.
    // We should implement a better solution in the future.
    return tk != "(" && tk != ")";
}

static bool add_extra_space(name const & tk) {
    // TODO(Leo): this is a hard-coded temporary solution for deciding whether extra
    // spaces should be added or not when pretty printing notation.
    // We should implement a better solution in the future.
    return tk != "," && tk != "(" && tk != ")";
}

static bool is_atomic_notation(notation_entry const & entry) {
    if (!entry.is_nud())
        return false;
    list<notation::transition> const & ts = entry.get_transitions();
    if (!is_nil(tail(ts)))
        return false;
    return head(ts).get_action().kind() == notation::action_kind::Skip;
}

auto pretty_fn::pp_notation(notation_entry const & entry, buffer<optional<expr>> & args) -> optional<result> {
    if (entry.is_numeral()) {
        return some(result(format(entry.get_num())));
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
        unsigned last_rbp  = inf_bp()-1;
        unsigned token_lbp = 0;
        bool extra_space   = false;
        bool last_is_skip  = false;
        bool last          = true;
        while (i > 0) {
            --i;
            format curr;
            notation::action const & a = ts[i].get_action();
            name const & tk = ts[i].get_token();
            switch (a.kind()) {
            case notation::action_kind::Skip:
                curr = format(tk);
                if (last) {
                    last_rbp     = inf_bp();
                    last_is_skip = true;
                }
                break;
            case notation::action_kind::Expr:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    expr e = *args.back();
                    args.pop_back();
                    result e_r   = pp_notation_child(e, token_lbp, a.rbp());
                    format e_fmt = e_r.fmt();
                    curr = format(tk);
                    // we add space after the token only when
                    // 1- add_extra_space(tk) is true AND
                    // 2- tk is the first token in a nud notation
                    if (add_extra_space(tk) && (!entry.is_nud() || i != 0 || m_extra_spaces))
                        curr = curr + space();
                    curr = curr + e_fmt;
                    if (last)
                        last_rbp = a.rbp();
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
                    if (!matched_once)
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
                        if (add_extra_space(*t) && m_extra_spaces)
                            curr = space() + curr;
                        curr_lbp = get_some_precedence(m_token_table, *t);
                    }
                    unsigned j       = rec_args.size();
                    format sep_fmt   = format(a.get_sep());
                    unsigned sep_lbp = get_some_precedence(m_token_table, a.get_sep());
                    while (j > 0) {
                        --j;
                        result arg_res = pp_notation_child(rec_args[j], curr_lbp, a.rbp());
                        if (j == 0) {
                            if (add_extra_space_first(tk) && (!entry.is_nud() || i != 0 || m_extra_spaces))
                                curr = format(tk) + space() + arg_res.fmt() + curr;
                            else
                                curr = format(tk) + arg_res.fmt() + curr;
                        } else {
                            curr = sep_fmt + space() + arg_res.fmt() + curr;
                        }
                        if (j > 0 && add_extra_space(a.get_sep()))
                            curr = space() + curr;
                        curr_lbp = sep_lbp;
                    }
                    break;
                }
            case notation::action_kind::Binder:
                if (locals.size() != 1)
                    return optional<result>();
                curr = format(tk) + pp_binders(locals);
                break;
            case notation::action_kind::Binders:
                curr = format(tk) + pp_binders(locals);
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
                    result e_r   = pp_notation_child(e, token_lbp, a.rbp());
                    format e_fmt = e_r.fmt();
                    curr = format(tk) + space() + e_fmt;
                    if (last)
                        last_rbp = a.rbp();
                    break;
                }
            case notation::action_kind::Ext:
            case notation::action_kind::LuaExt:
                return optional<result>();
            }
            token_lbp = get_some_precedence(m_token_table, tk);
            if (last) {
                fmt = curr;
                last = false;
            } else {
                if (extra_space)
                    curr = curr + space();
                fmt = curr + fmt;
            }
            if (m_extra_spaces || !last_is_skip)
                extra_space = add_extra_space(tk);
        }
        unsigned first_lbp = inf_bp();
        if (!entry.is_nud()) {
            first_lbp = token_lbp;
            lean_assert(!last);
            if (args.size() != 1 || !args.back())
                return optional<result>();
            expr e = *args.back();
            args.pop_back();
            format e_fmt = pp_notation_child(e, token_lbp, 0).fmt();
            if (m_extra_spaces || !last_is_skip)
                fmt = e_fmt + space() + fmt;
            else
                fmt = e_fmt + fmt;
        }
        return optional<result>(result(first_lbp, last_rbp, fmt));
    }
}

auto pretty_fn::pp_notation(expr const & e) -> optional<result> {
    if (!m_notation || is_var(e))
        return optional<result>();
    for (notation_entry const & entry : get_notation_entries(m_env, head_index(e))) {
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

auto pretty_fn::pp_abbreviation(expr const & e, name const & abbrev, bool fn, unsigned bp, bool ignore_hide) -> result {
    declaration const & d = m_env.get(abbrev);
    unsigned num_univs    = d.get_num_univ_params();
    buffer<level> ls;
    for (unsigned i = 0; i < num_univs; i++)
        ls.push_back(mk_meta_univ(name("?l", i+1)));
    expr r = mk_constant(abbrev, to_list(ls));
    if (fn)
        r = mk_app(r, app_arg(e));
    return pp_child(r, bp, ignore_hide);
}

static bool is_pp_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::App:
    case expr_kind::Lambda:
    case expr_kind::Pi:
    case expr_kind::Macro:
        return false;
    default:
        return true;
    }
}

auto pretty_fn::pp(expr const & e, bool ignore_hide) -> result {
    check_system("pretty printer");
    if ((m_depth >= m_max_depth ||
         m_num_steps > m_max_steps ||
         (m_hide_full_terms && !ignore_hide && !has_expr_metavar_relaxed(e))) &&
        !is_pp_atomic(e)) {
        return result(m_unicode ? *g_ellipsis_n_fmt : *g_ellipsis_fmt);
    }
    flet<unsigned> let_d(m_depth, m_depth+1);
    m_num_steps++;

    if (auto n = is_abbreviated(e))
        return pp_abbreviation(e, *n, false);

    if (auto r = pp_notation(e))
        return *r;

    if (is_placeholder(e))  return result(*g_placeholder_fmt);
    if (is_show(e))         return pp_show(e);
    if (is_have(e))         return pp_have(e);
    if (is_let(e))          return pp_let(e);
    if (is_typed_expr(e))   return pp(get_typed_expr_expr(e));
    if (is_let_value(e))    return pp(get_let_value_expr(e));
    if (m_numerals)
        if (auto n = to_num(e)) return pp_num(*n);
    if (m_num_nat_coe)
        if (auto k = to_unsigned(e))
            return format(*k);
    if (!m_metavar_args && is_meta(e))
        return pp_meta(get_app_fn(e));

    switch (e.kind()) {
    case expr_kind::Var:       return pp_var(e);
    case expr_kind::Sort:      return pp_sort(e);
    case expr_kind::Constant:  return pp_const(e);
    case expr_kind::Meta:      return pp_meta(e);
    case expr_kind::Local:     return pp_local(e);
    case expr_kind::App:       return pp_app(e);
    case expr_kind::Lambda:    return pp_lambda(e);
    case expr_kind::Pi:        return pp_pi(e);
    case expr_kind::Macro:     return pp_macro(e);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

pretty_fn::pretty_fn(environment const & env, options const & o):
    m_env(env), m_tc(env), m_token_table(get_token_table(env)) {
    set_options_core(o);
    m_meta_prefix   = "M";
    m_next_meta_idx = 1;
}

// Custom beta reduction procedure for the pretty printer.
// We don't want to reduce application in show annotations.
class pp_beta_reduce_fn : public replace_visitor {
    virtual expr visit_meta(expr const & e) { return e; }
    virtual expr visit_local(expr const & e) { return e; }

    virtual expr visit_macro(expr const & e) {
        if (is_show_annotation(e) && is_app(get_annotation_arg(e))) {
            expr const & n = get_annotation_arg(e);
            expr new_fn  = visit(app_fn(n));
            expr new_arg = visit(app_arg(n));
            return mk_show_annotation(mk_app(new_fn, new_arg));
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

    virtual expr visit_app(expr const & e) {
        expr new_e = replace_visitor::visit_app(e);
        if (is_head_beta(new_e))
            return visit(head_beta_reduce(new_e));
        else
            return new_e;
    }
};

format pretty_fn::operator()(expr const & e) {
    m_depth = 0; m_num_steps = 0;
    if (m_beta)
        return pp_child(purify(pp_beta_reduce_fn()(e)), 0).fmt();
    else
        return pp_child(purify(e), 0).fmt();
}

formatter_factory mk_pretty_formatter_factory() {
    return [](environment const & env, options const & o) { // NOLINT
        auto fn_ptr = std::make_shared<pretty_fn>(env, o);
        return formatter(o, [=](expr const & e, options const & new_o) {
                fn_ptr->set_options(new_o);
                return (*fn_ptr)(e);
            });
    };
}

static options mk_options(bool detail) {
    options opts;
    if (detail) {
        opts = opts.update(name{"pp", "implicit"}, true);
        opts = opts.update(name{"pp", "notation"}, false);
    }
    return opts;
}

static void pp_core(environment const & env, expr const & e, bool detail) {
    io_state ios(mk_pretty_formatter_factory(), mk_options(detail));
    regular(env, ios) << e << "\n";
}

static void pp_core(environment const & env, goal const & g, bool detail) {
    io_state ios(mk_pretty_formatter_factory(), mk_options(detail));
    regular(env, ios) << g << "\n";
}

static void pp_core(environment const & env, proof_state const & s, bool detail) {
    io_state ios(mk_pretty_formatter_factory(), mk_options(detail));
    regular(env, ios) << s.pp(env, ios) << "\n";
}
}
// for debugging purposes
void pp(lean::environment const & env, lean::expr const & e) { lean::pp_core(env, e, false); }
void pp(lean::environment const & env, lean::goal const & g) { lean::pp_core(env, g, false); }
void pp(lean::environment const & env, lean::proof_state const & s) { lean::pp_core(env, s, false); }
void pp_detail(lean::environment const & env, lean::expr const & e) { lean::pp_core(env, e, true); }
void pp_detail(lean::environment const & env, lean::goal const & g) { lean::pp_core(env, g, true); }
void pp_detail(lean::environment const & env, lean::proof_state const & s) { lean::pp_core(env, s, true); }
