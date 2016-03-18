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
#include "util/fresh_name.h"
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

expr mk_aux_type_metavar_for(expr const & t) {
    expr new_type = replace_range(t, mk_sort(mk_meta_univ(mk_fresh_name())));
    name n        = mk_fresh_name();
    return mk_metavar(n, new_type);
}

expr mk_aux_metavar_for(expr const & t) {
    unsigned num  = get_arity(t);
    expr r        = mk_app_vars(mk_aux_type_metavar_for(t), num);
    expr new_type = replace_range(t, r);
    name n        = mk_fresh_name();
    return mk_metavar(n, new_type);
}

expr mk_pi_for(expr const & meta) {
    lean_assert(is_meta(meta));
    buffer<expr> margs;
    expr const & m     = get_app_args(meta, margs);
    expr const & mtype = mlocal_type(m);
    expr maux1         = mk_aux_type_metavar_for(mtype);
    expr dontcare;
    expr tmp_pi        = mk_pi(mk_fresh_name(), mk_app_vars(maux1, margs.size()), dontcare); // trick for "extending" the context
    expr mtype2        = replace_range(mtype, tmp_pi); // trick for "extending" the context
    expr maux2         = mk_aux_type_metavar_for(mtype2);
    expr A             = mk_app(maux1, margs);
    margs.push_back(Var(0));
    expr B             = mk_app(maux2, margs);
    return mk_pi(mk_fresh_name(), A, B);
}

optional<expr> type_checker::expand_macro(expr const & m) {
    lean_assert(is_macro(m));
    return macro_def(m).expand(m, m_old_tc_ctx);
}

/**
   \brief Return the body of the given binder, where the free variable #0 is replaced with a fresh local constant.
   It also returns the fresh local constant.
*/
pair<expr, expr> type_checker::open_binding_body(expr const & e) {
    expr local     = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), binding_info(e));
    return mk_pair(instantiate(binding_body(e), local), local);
}

/**
   \brief Make sure \c e "is" a sort, and return the corresponding sort.
   If \c e is not a sort, then the whnf procedure is invoked.

   \remark \c s is used to extract position (line number information) when an
   error message is produced
*/
expr type_checker::ensure_sort_core(expr e, expr const & s) {
    if (is_sort(e))
        return e;
    auto new_e = whnf(e);
    if (is_sort(new_e)) {
        return new_e;
    } else {
        throw_kernel_exception(m_env, s, [=](formatter const & fmt) { return pp_type_expected(fmt, s); });
    }
}

/** \brief Similar to \c ensure_sort, but makes sure \c e "is" a Pi. */
expr type_checker::ensure_pi_core(expr e, expr const & s) {
    if (is_pi(e))
        return e;
    auto new_e = whnf(e);
    if (is_pi(new_e)) {
        return new_e;
    } else {
        throw_kernel_exception(m_env, s, [=](formatter const & fmt) { return pp_function_expected(fmt, s); });
    }
}

static constexpr char const * g_macro_error_msg = "failed to type check macro expansion";

void type_checker::check_level(level const & l, expr const & s) {
    if (auto n1 = get_undef_global(l, m_env))
        throw_kernel_exception(m_env, sstream() << "invalid reference to undefined global universe level '" << *n1 << "'", s);
    if (m_params) {
        if (auto n2 = get_undef_param(l, *m_params))
            throw_kernel_exception(m_env, sstream() << "invalid reference to undefined universe level parameter '"
                                   << *n2 << "'", s);
    }
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

expr type_checker::infer_macro(expr const & e, bool infer_only) {
    auto def = macro_def(e);
    auto t   = def.check_type(e, m_old_tc_ctx, infer_only);
    if (!infer_only && def.trust_level() >= m_env.trust_lvl()) {
        throw_kernel_exception(m_env, "declaration contains macro with trust-level higher than the one allowed "
                               "(possible solution: unfold macro, or increase trust-level)", e);
    }
    return t;
}

expr type_checker::infer_lambda(expr const & _e, bool infer_only) {
    buffer<expr> es, ds, ls;
    expr e = _e;
    while (is_lambda(e)) {
        es.push_back(e);
        ds.push_back(binding_domain(e));
        expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr l = mk_local(mk_fresh_name(), binding_name(e), d, binding_info(e));
        ls.push_back(l);
        if (!infer_only) {
            ensure_sort_core(infer_type_core(d, infer_only), d);
        }
        e = binding_body(e);
    }
    expr r = infer_type_core(instantiate_rev(e, ls.size(), ls.data()), infer_only);
    r = abstract_locals(r, ls.size(), ls.data());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = mk_pi(binding_name(es[i]), ds[i], r, binding_info(es[i]));
    }
    return r;
}

expr type_checker::infer_pi(expr const & _e, bool infer_only) {
    buffer<expr>  ls;
    buffer<level> us;
    expr e = _e;
    while (is_pi(e)) {
        expr d  = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr t1 = ensure_sort_core(infer_type_core(d, infer_only), d);
        us.push_back(sort_level(t1));
        expr l  = mk_local(mk_fresh_name(), binding_name(e), d, binding_info(e));
        ls.push_back(l);
        e = binding_body(e);
    }
    e = instantiate_rev(e, ls.size(), ls.data());
    expr s  = ensure_sort_core(infer_type_core(e, infer_only), e);
    level r = sort_level(s);
    unsigned i = ls.size();
    while (i > 0) {
        --i;
        r = m_env.impredicative() ? mk_imax(us[i], r) : mk_max(us[i], r);
    }
    return mk_sort(r);
}

expr type_checker::infer_app(expr const & e, bool infer_only) {
    if (!infer_only) {
        expr f_type = ensure_pi_core(infer_type_core(app_fn(e), infer_only), e);
        expr a_type = infer_type_core(app_arg(e), infer_only);
        expr d_type = binding_domain(f_type);
        if (!is_def_eq(a_type, d_type)) {
            throw_kernel_exception(m_env, e,
                                   [=](formatter const & fmt) {
                                       return pp_app_type_mismatch(fmt, e, f_type, app_arg(e), a_type, true);
                                   });
        }
        return instantiate(binding_body(f_type), app_arg(e));
    } else {
        buffer<expr> args;
        expr const & f = get_app_args(e, args);
        expr f_type    = infer_type_core(f, true);
        unsigned j        = 0;
        unsigned nargs    = args.size();
        for (unsigned i = 0; i < nargs; i++) {
            if (is_pi(f_type)) {
                f_type = binding_body(f_type);
            } else {
                f_type = instantiate_rev(f_type, i-j, args.data()+j);
                f_type = ensure_pi_core(f_type, e);
                f_type = binding_body(f_type);
                j = i;
            }
        }
        return instantiate_rev(f_type, nargs-j, args.data()+j);
    }
}

expr type_checker::infer_let(expr const & e, bool infer_only) {
    if (!infer_only) {
        ensure_sort_core(infer_type_core(let_type(e), infer_only), e);
        expr v_type = infer_type_core(let_value(e), infer_only);
        // TODO(Leo): we will remove justifications in the future.
        if (!is_def_eq(v_type, let_type(e))) {
            throw_kernel_exception(m_env, e,
                                   [=](formatter const & fmt) {
                                       return pp_def_type_mismatch(fmt, let_name(e), let_type(e), v_type, true);
                                   });
        }
    }
    return infer_type_core(instantiate(let_body(e), let_value(e)), infer_only);
}

/**
   \brief Return type of expression \c e, if \c infer_only is false, then it also check whether \c e is type correct or not.

   \pre closed(e)
*/
expr type_checker::infer_type_core(expr const & e, bool infer_only) {
    if (is_var(e))
        throw_kernel_exception(m_env, "type checker does not support free variables, replace them with local constants before invoking it", e);

    lean_assert(closed(e));
    check_system("type checker");

    if (m_memoize) {
        auto it = m_infer_type_cache[infer_only].find(e);
        if (it != m_infer_type_cache[infer_only].end())
            return it->second;
    }

    expr r;
    switch (e.kind()) {
    case expr_kind::Local: case expr_kind::Meta:  r = mlocal_type(e);  break;
    case expr_kind::Var:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Sort:
        if (!infer_only) check_level(sort_level(e), e);
        r = mk_sort(mk_succ(sort_level(e)));
        break;
    case expr_kind::Constant:  r = infer_constant(e, infer_only);       break;
    case expr_kind::Macro:     r = infer_macro(e, infer_only);          break;
    case expr_kind::Lambda:    r = infer_lambda(e, infer_only);         break;
    case expr_kind::Pi:        r = infer_pi(e, infer_only);             break;
    case expr_kind::App:       r = infer_app(e, infer_only);            break;
    case expr_kind::Let:       r = infer_let(e, infer_only);            break;
    }

    if (m_memoize)
        m_infer_type_cache[infer_only].insert(mk_pair(e, r));
    return r;
}

expr type_checker::infer_type(expr const & e) {
    return infer_type_core(e, true);
}

expr type_checker::check(expr const & e, level_param_names const & ps) {
    flet<level_param_names const *> updt(m_params, &ps);
    return infer_type_core(e, false);
}

expr type_checker::check_ignore_undefined_universes(expr const & e) {
    flet<level_param_names const *> updt(m_params, nullptr);
    return infer_type_core(e, false);
}

expr type_checker::ensure_sort(expr const & e, expr const & s) {
    return ensure_sort_core(e, s);
}

expr type_checker::ensure_pi(expr const & e, expr const & s) {
    return ensure_pi_core(e, s);
}

bool type_checker::is_def_eq(expr const & t, expr const & s) {
    return m_conv->is_def_eq(t, s, *this);
}

bool type_checker::is_def_eq_types(expr const & t, expr const & s) {
    expr t1 = infer_type_core(t, true);
    expr t2 = infer_type_core(s, true);
    return m_conv->is_def_eq(t1, t2, *this);
}

/** \brief Return true iff \c e is a proposition */
bool type_checker::is_prop(expr const & e) {
    return m_env.impredicative() && whnf(infer_type(e)) == mk_Prop();
}

expr type_checker::whnf(expr const & t) {
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

type_checker::type_checker(environment const & env, std::unique_ptr<converter> && conv, bool memoize):
    m_env(env), m_conv(std::move(conv)), m_old_tc_ctx(*this), m_tc_ctx(*this),
    m_memoize(memoize), m_params(nullptr) {
}

type_checker::type_checker(environment const & env, bool memoize):
    type_checker(env, std::unique_ptr<converter>(new default_converter(env, memoize)), memoize) {}

type_checker::~type_checker() {}

optional<expr> type_checker::is_stuck(expr const & e) {
    return m_conv->is_stuck(e, *this);
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

certified_declaration check(environment const & env, declaration const & d, name_predicate const & pred) {
    if (d.is_definition())
        check_no_mlocal(env, d.get_name(), d.get_value(), false);
    check_no_mlocal(env, d.get_name(), d.get_type(), true);
    check_name(env, d.get_name());
    check_duplicated_params(env, d);
    type_checker checker(env, std::unique_ptr<converter>(new hint_converter<default_converter>(env, pred)));
    expr sort = checker.check(d.get_type(), d.get_univ_params());
    checker.ensure_sort(sort, d.get_type());
    if (d.is_definition()) {
        expr val_type = checker.check(d.get_value(), d.get_univ_params());
        if (!checker.is_def_eq(val_type, d.get_type())) {
            throw_kernel_exception(env, d.get_value(), [=](formatter const & fmt) {
                    return pp_def_type_mismatch(fmt, d.get_name(), d.get_type(), val_type, true);
                });
        }
    }
    return certified_declaration(env.get_id(), d);
}

certified_declaration check(environment const & env, declaration const & d) {
    return check(env, d, [](name const &) { return false; });
}

void initialize_type_checker() {
}

void finalize_type_checker() {
}
}
