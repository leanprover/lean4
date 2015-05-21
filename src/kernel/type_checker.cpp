/*
Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/interrupt.h"
#include "util/lbool.h"
#include "util/flet.h"
#include "util/sstream.h"
#include "util/scoped_map.h"
#include "kernel/type_checker.h"
#include "kernel/default_converter.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "kernel/metavar.h"
#include "kernel/error_msgs.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"

namespace lean {
expr replace_range(expr const & type, expr const & new_range) {
    if (is_pi(type))
        return update_binding(type, binding_domain(type), replace_range(binding_body(type), new_range));
    else
        return new_range;
}

/** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
unsigned get_arity(expr type) {
    unsigned r = 0;
    while (is_pi(type)) {
        type = binding_body(type);
        r++;
    }
    return r;
}

expr mk_aux_type_metavar_for(name_generator & ngen, expr const & t) {
    expr new_type = replace_range(t, mk_sort(mk_meta_univ(ngen.next())));
    name n        = ngen.next();
    return mk_metavar(n, new_type);
}

expr mk_aux_metavar_for(name_generator & ngen, expr const & t) {
    unsigned num  = get_arity(t);
    expr r        = mk_app_vars(mk_aux_type_metavar_for(ngen, t), num);
    expr new_type = replace_range(t, r);
    name n        = ngen.next();
    return mk_metavar(n, new_type);
}

expr mk_pi_for(name_generator & ngen, expr const & meta) {
    lean_assert(is_meta(meta));
    buffer<expr> margs;
    expr const & m     = get_app_args(meta, margs);
    expr const & mtype = mlocal_type(m);
    expr maux1         = mk_aux_type_metavar_for(ngen, mtype);
    expr dontcare;
    expr tmp_pi        = mk_pi(ngen.next(), mk_app_vars(maux1, margs.size()), dontcare); // trick for "extending" the context
    expr mtype2        = replace_range(mtype, tmp_pi); // trick for "extending" the context
    expr maux2         = mk_aux_type_metavar_for(ngen, mtype2);
    expr A             = mk_app(maux1, margs);
    margs.push_back(Var(0));
    expr B             = mk_app(maux2, margs);
    return mk_pi(ngen.next(), A, B);
}

optional<expr> type_checker::expand_macro(expr const & m) {
    lean_assert(is_macro(m));
    return macro_def(m).expand(m, m_tc_ctx);
}

/**
   \brief Return the body of the given binder, where the free variable #0 is replaced with a fresh local constant.
   It also returns the fresh local constant.
*/
pair<expr, expr> type_checker::open_binding_body(expr const & e) {
    expr local     = mk_local(m_gen.next(), binding_name(e), binding_domain(e), binding_info(e));
    return mk_pair(instantiate(binding_body(e), local), local);
}

constraint type_checker::mk_eq_cnstr(expr const & lhs, expr const & rhs, justification const & j) {
    return ::lean::mk_eq_cnstr(lhs, rhs, j);
}

/**
   \brief Make sure \c e "is" a sort, and return the corresponding sort.
   If \c e is not a sort, then the whnf procedure is invoked. Then, there are
   two options: the normalize \c e is a sort, or it is a meta. If it is a meta,
   a new constraint is created forcing it to be a sort.

   \remark \c s is used to extract position (line number information) when an
   error message is produced
*/
pair<expr, constraint_seq> type_checker::ensure_sort_core(expr e, expr const & s) {
    if (is_sort(e))
        return to_ecs(e);
    auto ecs = whnf(e);
    if (is_sort(ecs.first)) {
        return ecs;
    } else if (is_meta(ecs.first)) {
        expr r = mk_sort(mk_meta_univ(m_gen.next()));
        justification j = mk_justification(s,
                                           [=](formatter const & fmt, substitution const & subst) {
                                               return pp_type_expected(fmt, substitution(subst).instantiate(s));
                                           });
        return to_ecs(r, mk_eq_cnstr(ecs.first, r, j), ecs.second);
    } else {
        throw_kernel_exception(m_env, s, [=](formatter const & fmt) { return pp_type_expected(fmt, s); });
    }
}

/** \brief Similar to \c ensure_sort, but makes sure \c e "is" a Pi. */
pair<expr, constraint_seq> type_checker::ensure_pi_core(expr e, expr const & s) {
    if (is_pi(e))
        return to_ecs(e);
    auto ecs = whnf(e);
    if (is_pi(ecs.first)) {
        return ecs;
    } else if (auto m = is_stuck(ecs.first)) {
        expr r             = mk_pi_for(m_gen, *m);
        justification j    = mk_justification(s, [=](formatter const & fmt, substitution const & subst) {
                return pp_function_expected(fmt, substitution(subst).instantiate(s));
            });
        return to_ecs(r, mk_eq_cnstr(ecs.first, r, j), ecs.second);
    } else {
        throw_kernel_exception(m_env, s, [=](formatter const & fmt) { return pp_function_expected(fmt, s); });
    }
}

static constexpr char const * g_macro_error_msg = "failed to type check macro expansion";

justification type_checker::mk_macro_jst(expr const & e) {
    return mk_justification(e, [=](formatter const &, substitution const &) {
            return format(g_macro_error_msg);
        });
}

void type_checker::check_level(level const & l, expr const & s) {
    if (auto n1 = get_undef_global(l, m_env))
        throw_kernel_exception(m_env, sstream() << "invalid reference to undefined global universe level '" << *n1 << "'", s);
    if (m_params) {
        if (auto n2 = get_undef_param(l, *m_params))
            throw_kernel_exception(m_env, sstream() << "invalid reference to undefined universe level parameter '"
                                   << *n2 << "'", s);
    }
}

app_delayed_justification::app_delayed_justification(expr const & e, expr const & arg, expr const & f_type,
                                                     expr const & a_type):
    m_e(e), m_arg(arg), m_fn_type(f_type), m_arg_type(a_type) {}

justification mk_app_justification(expr const & e, expr const & arg, expr const & d_type, expr const & a_type) {
    auto pp_fn = [=](formatter const & fmt, substitution const & subst) {
        substitution s(subst);
        return pp_app_type_mismatch(fmt, s.instantiate(e), s.instantiate(arg), s.instantiate(d_type), s.instantiate(a_type));
    };
    return mk_justification(e, pp_fn);
}

justification app_delayed_justification::get() {
    if (!m_jst) {
        // We should not have a reference to this object inside the closure.
        // So, we create the following locals that will be captured by the closure instead of 'this'.
        m_jst = mk_app_justification(m_e, m_arg, binding_domain(m_fn_type), m_arg_type);
    }
    return *m_jst;
}

expr type_checker::infer_constant(expr const & e, bool infer_only) {
    declaration d    = m_env.get(const_name(e));
    auto const & ps = d.get_univ_params();
    auto const & ls = const_levels(e);
    if (length(ps) != length(ls))
        throw_kernel_exception(m_env, sstream() << "incorrect number of universe levels parameters for '"
                               << const_name(e) << "', #"
                               << length(ps)  << " expected, #" << length(ls) << " provided");
    if (!infer_only) {
        for (level const & l : ls)
            check_level(l, e);
    }
    return instantiate_type_univ_params(d, ls);
}

pair<expr, constraint_seq> type_checker::infer_macro(expr const & e, bool infer_only) {
    auto def = macro_def(e);
    pair<expr, constraint_seq> tcs = def.check_type(e, m_tc_ctx, infer_only);
    expr t            = tcs.first;
    constraint_seq cs = tcs.second;
    if (!infer_only && def.trust_level() >= m_env.trust_lvl()) {
        throw_kernel_exception(m_env, "declaration contains macro with trust-level higher than the one allowed "
                               "(possible solution: unfold macro, or increase trust-level)", e);
    }
    return mk_pair(t, cs);
}

pair<expr, constraint_seq> type_checker::infer_lambda(expr const & _e, bool infer_only) {
    buffer<expr> es, ds, ls;
    expr e = _e;
    constraint_seq cs;
    while (is_lambda(e)) {
        es.push_back(e);
        ds.push_back(binding_domain(e));
        expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr l = mk_local(m_gen.next(), binding_name(e), d, binding_info(e));
        ls.push_back(l);
        if (!infer_only) {
            pair<expr, constraint_seq> dtcs = infer_type_core(d, infer_only);
            pair<expr, constraint_seq> scs  = ensure_sort_core(dtcs.first, d);
            cs = cs + scs.second + dtcs.second;
        }
        e = binding_body(e);
    }
    pair<expr, constraint_seq> rcs = infer_type_core(instantiate_rev(e, ls.size(), ls.data()), infer_only);
    cs = cs + rcs.second;
    expr r = abstract_locals(rcs.first, ls.size(), ls.data());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = mk_pi(binding_name(es[i]), ds[i], r, binding_info(es[i]));
    }
    return mk_pair(r, cs);
}

pair<expr, constraint_seq> type_checker::infer_pi(expr const & _e, bool infer_only) {
    buffer<expr>  ls;
    buffer<level> us;
    expr e = _e;
    constraint_seq cs;
    while (is_pi(e)) {
        expr d                          = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        pair<expr, constraint_seq> dtcs = infer_type_core(d, infer_only);
        pair<expr, constraint_seq> scs  = ensure_sort_core(dtcs.first, d);
        cs = cs + scs.second + dtcs.second;
        expr t1 = scs.first;
        us.push_back(sort_level(t1));
        expr l  = mk_local(m_gen.next(), binding_name(e), d, binding_info(e));
        ls.push_back(l);
        e = binding_body(e);
    }
    e = instantiate_rev(e, ls.size(), ls.data());
    pair<expr, constraint_seq> etcs = infer_type_core(e, infer_only);
    pair<expr, constraint_seq> scs  = ensure_sort_core(etcs.first, e);
    cs = cs + scs.second + etcs.second;
    level r = sort_level(scs.first);
    unsigned i = ls.size();
    while (i > 0) {
        --i;
        r = m_env.impredicative() ? mk_imax(us[i], r) : mk_max(us[i], r);
    }
    return mk_pair(mk_sort(r), cs);
}

pair<expr, constraint_seq> type_checker::infer_app(expr const & e, bool infer_only) {
    if (!infer_only) {
        pair<expr, constraint_seq> ftcs = infer_type_core(app_fn(e), infer_only);
        pair<expr, constraint_seq> pics = ensure_pi_core(ftcs.first, e);
        expr f_type = pics.first;
        pair<expr, constraint_seq> acs  = infer_type_core(app_arg(e), infer_only);
        expr a_type = acs.first;
        app_delayed_justification jst(e, app_arg(e), f_type, a_type);
        expr d_type = binding_domain(pics.first);
        pair<bool, constraint_seq> dcs  = is_def_eq(a_type, d_type, jst);
        if (!dcs.first) {
            throw_kernel_exception(m_env, e,
                                   [=](formatter const & fmt) {
                                       return pp_app_type_mismatch(fmt, e, app_arg(e), d_type, a_type);
                                   });
        }
        return mk_pair(instantiate(binding_body(pics.first), app_arg(e)),
                       pics.second + ftcs.second + dcs.second + acs.second);
    } else {
        buffer<expr> args;
        expr const & f = get_app_args(e, args);
        pair<expr, constraint_seq> ftcs = infer_type_core(f, true);
        expr f_type       = ftcs.first;
        constraint_seq cs = ftcs.second;
        unsigned j        = 0;
        unsigned nargs    = args.size();
        for (unsigned i = 0; i < nargs; i++) {
            if (is_pi(f_type)) {
                f_type = binding_body(f_type);
            } else {
                f_type = instantiate_rev(f_type, i-j, args.data()+j);
                pair<expr, constraint_seq> pics = ensure_pi_core(f_type, e);
                f_type = pics.first;
                cs     = pics.second + cs;
                f_type = binding_body(f_type);
                j = i;
            }
        }
        expr r = instantiate_rev(f_type, nargs-j, args.data()+j);
        return mk_pair(r, cs);
    }
}

expr type_checker::infer_type_core(expr const & e, bool infer_only, constraint_seq & cs) {
    auto r = infer_type_core(e, infer_only);
    cs = cs + r.second;
    return r.first;
}

/**
   \brief Return type of expression \c e, if \c infer_only is false, then it also check whether \c e is type correct or not.

   \pre closed(e)
*/
pair<expr, constraint_seq> type_checker::infer_type_core(expr const & e, bool infer_only) {
    if (is_var(e))
        throw_kernel_exception(m_env, "type checker does not support free variables, replace them with local constants before invoking it", e);

    lean_assert(closed(e));
    check_system("type checker");

    if (m_memoize) {
        auto it = m_infer_type_cache[infer_only].find(e);
        if (it != m_infer_type_cache[infer_only].end())
            return it->second;
    }

    pair<expr, constraint_seq> r;
    switch (e.kind()) {
    case expr_kind::Local: case expr_kind::Meta:  r.first = mlocal_type(e);  break;
    case expr_kind::Var:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Sort:
        if (!infer_only) check_level(sort_level(e), e);
        r.first = mk_sort(mk_succ(sort_level(e)));
        break;
    case expr_kind::Constant:  r.first = infer_constant(e, infer_only); break;
    case expr_kind::Macro:     r = infer_macro(e, infer_only);          break;
    case expr_kind::Lambda:    r = infer_lambda(e, infer_only);         break;
    case expr_kind::Pi:        r = infer_pi(e, infer_only);             break;
    case expr_kind::App:       r = infer_app(e, infer_only);            break;
    }

    if (m_memoize)
        m_infer_type_cache[infer_only].insert(mk_pair(e, r));

    return r;
}

pair<expr, constraint_seq> type_checker::infer_type(expr const & e) {
    return infer_type_core(e, true);
}

pair<expr, constraint_seq> type_checker::check(expr const & e, level_param_names const & ps) {
    flet<level_param_names const *> updt(m_params, &ps);
    return infer_type_core(e, false);
}

pair<expr, constraint_seq> type_checker::check_ignore_undefined_universes(expr const & e) {
    flet<level_param_names const *> updt(m_params, nullptr);
    return infer_type_core(e, false);
}

pair<expr, constraint_seq> type_checker::ensure_sort(expr const & e, expr const & s) {
    return ensure_sort_core(e, s);
}

pair<expr, constraint_seq> type_checker::ensure_pi(expr const & e, expr const & s) {
    return ensure_pi_core(e, s);
}

/** \brief Return true iff \c t and \c s are definitionally equal */
pair<bool, constraint_seq> type_checker::is_def_eq(expr const & t, expr const & s, delayed_justification & jst) {
    return m_conv->is_def_eq(t, s, *this, jst);
}

pair<bool, constraint_seq> type_checker::is_def_eq(expr const & t, expr const & s) {
    return m_conv->is_def_eq(t, s, *this);
}

pair<bool, constraint_seq> type_checker::is_def_eq(expr const & t, expr const & s, justification const & j) {
    as_delayed_justification djst(j);
    return is_def_eq(t, s, djst);
}

pair<bool, constraint_seq> type_checker::is_def_eq_types(expr const & t, expr const & s, justification const & j) {
    auto tcs1 = infer_type_core(t, true);
    auto tcs2 = infer_type_core(s, true);
    as_delayed_justification djst(j);
    auto bcs  = m_conv->is_def_eq(tcs1.first, tcs2.first, *this, djst);
    return mk_pair(bcs.first, bcs.first ? bcs.second + tcs1.second + tcs2.second : constraint_seq());
}

/** \brief Return true iff \c e is a proposition */
pair<bool, constraint_seq> type_checker::is_prop(expr const & e) {
    auto tcs  = infer_type(e);
    auto wtcs = whnf(tcs.first);
    bool r    = wtcs.first == mk_Prop();
    if (r)
        return mk_pair(true, tcs.second + wtcs.second);
    else
        return mk_pair(false, constraint_seq());
}

pair<expr, constraint_seq> type_checker::whnf(expr const & t) {
    return m_conv->whnf(t, *this);
}

bool type_checker::is_opaque(declaration const & d) const {
    return m_conv->is_opaque(d);
}

bool type_checker::is_opaque(expr const & c) const {
    lean_assert(is_constant(c));
    if (auto d = m_env.find(const_name(c)))
        return d->is_definition() && is_opaque(*d);
    else
        return true;
}

type_checker::type_checker(environment const & env, name_generator && g, std::unique_ptr<converter> && conv, bool memoize):
    m_env(env), m_gen(g), m_conv(std::move(conv)), m_tc_ctx(*this),
    m_memoize(memoize), m_params(nullptr) {
}

type_checker::type_checker(environment const & env, name_generator && g, bool memoize):
    type_checker(env, std::move(g), std::unique_ptr<converter>(new default_converter(env, memoize)), memoize) {}

static name * g_tmp_prefix = nullptr;

type_checker::type_checker(environment const & env):
    type_checker(env, name_generator(*g_tmp_prefix), std::unique_ptr<converter>(new default_converter(env)), true) {}

type_checker::~type_checker() {}

optional<expr> type_checker::is_stuck(expr const & e) {
    if (is_meta(e)) {
        return some_expr(e);
    } else {
        return m_env.norm_ext().is_stuck(e, m_tc_ctx);
    }
}

void check_no_metavar(environment const & env, name const & n, expr const & e, bool is_type) {
    if (has_metavar(e))
        throw_kernel_exception(env, e, [=](formatter const & fmt) { return pp_decl_has_metavars(fmt, n, e, is_type); });
}

static void check_no_local(environment const & env, expr const & e) {
    if (has_local(e))
        throw_kernel_exception(env, "failed to add declaration to environment, it contains local constants", e);
}

void check_no_mlocal(environment const & env, name const & n, expr const & e, bool is_type) {
    check_no_metavar(env, n, e, is_type);
    check_no_local(env, e);
}

static void check_name(environment const & env, name const & n) {
    if (env.find(n))
        throw_already_declared(env, n);
}

static void check_duplicated_params(environment const & env, declaration const & d) {
    level_param_names ls = d.get_univ_params();
    while (!is_nil(ls)) {
        auto const & p = head(ls);
        ls = tail(ls);
        if (std::find(ls.begin(), ls.end(), p) != ls.end()) {
            throw_kernel_exception(env, sstream() << "failed to add declaration to environment, "
                                   << "duplicate universe level parameter: '"
                                   << p << "'", d.get_type());
        }
    }
}

certified_declaration check(environment const & env, declaration const & d, name_generator && g) {
    if (d.is_definition())
        check_no_mlocal(env, d.get_name(), d.get_value(), false);
    check_no_mlocal(env, d.get_name(), d.get_type(), true);
    check_name(env, d.get_name());
    check_duplicated_params(env, d);
    bool memoize = true;
    type_checker checker1(env, g.mk_child(), std::unique_ptr<converter>(new default_converter(env, memoize)));
    expr sort = checker1.check(d.get_type(), d.get_univ_params()).first;
    checker1.ensure_sort(sort, d.get_type());
    if (d.is_definition()) {
        type_checker checker2(env, g.mk_child(), std::unique_ptr<converter>(new default_converter(env, memoize)));
        expr val_type = checker2.check(d.get_value(), d.get_univ_params()).first;
        if (!checker2.is_def_eq(val_type, d.get_type()).first) {
            throw_kernel_exception(env, d.get_value(), [=](formatter const & fmt) {
                    return pp_def_type_mismatch(fmt, d.get_name(), d.get_type(), val_type);
                });
        }
    }
    return certified_declaration(env.get_id(), d);
}

certified_declaration check(environment const & env, declaration const & d) {
    return check(env, d, name_generator(*g_tmp_prefix));
}

void initialize_type_checker() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_type_checker() {
    delete g_tmp_prefix;
}
}
