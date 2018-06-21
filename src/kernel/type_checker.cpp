/*
Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "runtime/interrupt.h"
#include "runtime/sstream.h"
#include "runtime/flet.h"
#include "util/task.h"
#include "util/lbool.h"
#include "util/fresh_name.h"
#include "util/task_builder.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/quot.h"
#include "kernel/inductive/inductive.h"

namespace lean {
static name * g_kernel_fresh = nullptr;
static expr * g_dont_care    = nullptr;

/** \brief Return the body of the given binder, where the bound variable #0 is replaced with a fresh free variable.
    It also returns the fresh variable. */
pair<expr, expr> type_checker::open_binding_body(expr const & e) {
    expr fvar = m_lctx.mk_local_decl(m_name_generator, binding_name(e), binding_domain(e), binding_info(e));
    return mk_pair(instantiate(binding_body(e), fvar), fvar);
}

/** \brief Make sure \c e "is" a sort, and return the corresponding sort.
    If \c e is not a sort, then the whnf procedure is invoked.

    \remark \c s is used to extract position (line number information) when an
    error message is produced */
expr type_checker::ensure_sort_core(expr e, expr const & s) {
    if (is_sort(e))
        return e;
    auto new_e = whnf(e);
    if (is_sort(new_e)) {
        return new_e;
    } else {
        throw type_expected_exception(m_env, m_lctx, s);
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
        throw function_expected_exception(m_env, m_lctx, s);
    }
}

void type_checker::check_level(level const & l) {
    if (m_params) {
        if (auto n2 = get_undef_param(l, *m_params))
            throw kernel_exception(m_env, sstream() << "invalid reference to undefined universe level parameter '"
                                   << *n2 << "'");
    }
}

expr type_checker::infer_fvar(expr const & e) {
    if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
        return decl->get_type();
    } else {
        // TODO(Leo): delete after we refactor inductive datatype module
        return mlocal_type(e);
        throw kernel_exception(m_env, "unknown free variable");
    }
}

expr type_checker::infer_constant(expr const & e, bool infer_only) {
    declaration d    = m_env.get(const_name(e));
    auto const & ps = d.get_univ_params();
    auto const & ls = const_levels(e);
    if (length(ps) != length(ls))
        throw kernel_exception(m_env, sstream() << "incorrect number of universe levels parameters for '"
                               << const_name(e) << "', #"
                               << length(ps)  << " expected, #" << length(ls) << " provided");
    if (!infer_only) {
        if (m_non_meta_only && d.is_meta()) {
            throw kernel_exception(m_env, sstream() << "invalid definition, it uses meta declaration '"
                                   << const_name(e) << "'");
        }
        for (level const & l : ls)
            check_level(l);
    }
    return instantiate_type_univ_params(d, ls);
}

expr type_checker::infer_lambda(expr const & _e, bool infer_only) {
    flet<local_ctx> save_lctx(m_lctx, m_lctx);
    buffer<expr> fvars;
    expr e = _e;
    while (is_lambda(e)) {
        expr d    = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
        expr fvar = m_lctx.mk_local_decl(m_name_generator, binding_name(e), d, binding_info(e));
        fvars.push_back(fvar);
        if (!infer_only) {
            ensure_sort_core(infer_type_core(d, infer_only), d);
        }
        e = binding_body(e);
    }
    expr r = infer_type_core(instantiate_rev(e, fvars.size(), fvars.data()), infer_only);
    return m_lctx.mk_pi(fvars, r);
}

expr type_checker::infer_pi(expr const & _e, bool infer_only) {
    flet<local_ctx> save_lctx(m_lctx, m_lctx);
    buffer<expr> fvars;
    buffer<level> us;
    expr e = _e;
    while (is_pi(e)) {
        expr d  = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
        expr t1 = ensure_sort_core(infer_type_core(d, infer_only), d);
        us.push_back(sort_level(t1));
        expr fvar  = m_lctx.mk_local_decl(m_name_generator, binding_name(e), d, binding_info(e));
        fvars.push_back(fvar);
        e = binding_body(e);
    }
    e = instantiate_rev(e, fvars.size(), fvars.data());
    expr s  = ensure_sort_core(infer_type_core(e, infer_only), e);
    level r = sort_level(s);
    unsigned i = fvars.size();
    while (i > 0) {
        --i;
        r = mk_imax(us[i], r);
    }
    return mk_sort(r);
}

expr type_checker::infer_app(expr const & e, bool infer_only) {
    if (!infer_only) {
        expr f_type = ensure_pi_core(infer_type_core(app_fn(e), infer_only), e);
        expr a_type = infer_type_core(app_arg(e), infer_only);
        expr d_type = binding_domain(f_type);
        if (!is_def_eq(a_type, d_type)) {
            throw app_type_mismatch_exception(m_env, m_lctx, e);
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

expr type_checker::infer_let(expr const & _e, bool infer_only) {
    flet<local_ctx> save_lctx(m_lctx, m_lctx);
    buffer<expr> fvars;
    expr e = _e;
    while (is_let(e)) {
        expr type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
        expr val  = instantiate_rev(let_value(e), fvars.size(), fvars.data());
        expr fvar = m_lctx.mk_local_decl(m_name_generator, let_name(e), type, val);
        fvars.push_back(fvar);
        if (!infer_only) {
            ensure_sort_core(infer_type_core(type, infer_only), type);
            expr val_type = infer_type_core(val, infer_only);
            if (!is_def_eq(val_type, type)) {
                throw def_type_mismatch_exception(m_env, m_lctx, let_name(e), val_type, type);
            }
        }
        e = let_body(e);
    }
    expr r = infer_type_core(instantiate_rev(e, fvars.size(), fvars.data()), infer_only);
    return m_lctx.mk_pi(fvars, r);
}

expr type_checker::infer_proj(expr const & e, bool infer_only) {
    expr type = whnf(infer_type_core(proj_expr(e), infer_only));
    if (!proj_idx(e).is_small())
        throw invalid_proj_exception(m_env, m_lctx, e);
    unsigned idx = proj_idx(e).get_small_value();
    buffer<expr> args;
    expr const & I = get_app_args(type, args);
    if (!is_constant(I))
        throw invalid_proj_exception(m_env, m_lctx, e);
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(m_env, const_name(I));
    if (!decl)
        throw invalid_proj_exception(m_env, m_lctx, e);
    if (length(decl->m_intro_rules) != 1 || args.size() != decl->m_num_params)
        throw invalid_proj_exception(m_env, m_lctx, e);

    inductive::intro_rule cnstr = head(decl->m_intro_rules);
    declaration c_decl = m_env.get(inductive::intro_rule_name(cnstr));
    expr r = instantiate_type_univ_params(c_decl, const_levels(I));
    for (expr const & arg : args) {
        r = whnf(r);
        if (!is_pi(r)) throw invalid_proj_exception(m_env, m_lctx, e);
        r = instantiate(binding_body(r), arg);
    }
    for (unsigned i = 0; i < idx; i++) {
        r = whnf(r);
        if (!is_pi(r)) throw invalid_proj_exception(m_env, m_lctx, e);
        if (has_loose_bvars(binding_body(r)))
            r = instantiate(binding_body(r), mk_proj(i, proj_expr(e)));
        else
            r = binding_body(r);
    }
    r = whnf(r);
    if (!is_pi(r)) throw invalid_proj_exception(m_env, m_lctx, e);
    return binding_domain(r);
}

/** \brief Return type of expression \c e, if \c infer_only is false, then it also check whether \c e is type correct or not.
    \pre closed(e) */
expr type_checker::infer_type_core(expr const & e, bool infer_only) {
    if (is_bvar(e))
        throw kernel_exception(m_env, "type checker does not support loose bound variables, replace them with free variables before invoking it");

    lean_assert(!has_loose_bvars(e));
    check_system("type checker");

    if (m_memoize) {
        auto it = m_infer_type_cache[infer_only].find(e);
        if (it != m_infer_type_cache[infer_only].end())
            return it->second;
    }

    expr r;
    switch (e.kind()) {
    case expr_kind::Lit:      r = lit_type(e);    break;
    case expr_kind::MData:    r = infer_type_core(mdata_expr(e), infer_only); break;
    case expr_kind::Proj:     r = infer_proj(e, infer_only); break;
    case expr_kind::FVar:     r = infer_fvar(e);  break;
    case expr_kind::MVar:     r = mlocal_type(e); break;
    case expr_kind::BVar:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Sort:
        if (!infer_only) check_level(sort_level(e));
        r = mk_sort(mk_succ(sort_level(e)));
        break;
    case expr_kind::Const:    r = infer_constant(e, infer_only);       break;
    case expr_kind::Lambda:   r = infer_lambda(e, infer_only);         break;
    case expr_kind::Pi:       r = infer_pi(e, infer_only);             break;
    case expr_kind::App:      r = infer_app(e, infer_only);            break;
    case expr_kind::Let:      r = infer_let(e, infer_only);            break;

    case expr_kind::Quote:
        if (quote_is_reflected(e)) {
            expr type = infer_type_core(quote_value(e), true);
            level u   = sort_level(ensure_sort_core(infer_type_core(type, true), e));
            return mk_app(mk_constant(name("reflected"), {u}), type, quote_value(e));
        } else {
            return mk_constant(name("pexpr"));
        }
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

/** \brief Return true iff \c e is a proposition */
bool type_checker::is_prop(expr const & e) {
    return whnf(infer_type(e)) == mk_Prop();
}

/** \brief Apply normalizer extensions to \c e. */
optional<expr> type_checker::norm_ext(expr const & e) {
    if (m_env.is_quot_initialized()) {
        if (optional<expr> r = quot_reduce_rec(e, [&](expr const & e) { return whnf(e); })) {
            return r;
        }
    }
    return m_env.norm_ext()(e, *this);
}

expr type_checker::whnf_fvar(expr const & e) {
    if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
        if (optional<expr> const & v = decl->get_value()) {
            /* zeta-reduction */
            return *v;
        }
    }
    return e;
}

optional<expr> type_checker::reduce_proj(expr const & e) {
    if (!proj_idx(e).is_small())
        return none_expr();
    unsigned idx = proj_idx(e).get_small_value();
    expr c = whnf(proj_expr(e));
    buffer<expr> args;
    expr const & mk = get_app_args(c, args);
    if (!is_constant(mk))
        return none_expr();
    optional<name> I = inductive::is_intro_rule(m_env, const_name(mk));
    if (!I)
        return none_expr();
    inductive::inductive_decl decl = *inductive::is_inductive_decl(m_env, *I);
    if (decl.m_num_params + idx < args.size())
        return some_expr(args[decl.m_num_params + idx]);
    else
        return none_expr();
}

/** \brief Weak head normal form core procedure. It does not perform delta reduction nor normalization extensions. */
expr type_checker::whnf_core(expr const & e) {
    check_system("whnf");

    // handle easy cases
    switch (e.kind()) {
    case expr_kind::BVar: case expr_kind::Sort:  case expr_kind::MVar:
    case expr_kind::Pi:   case expr_kind::Const: case expr_kind::Lambda:
    case expr_kind::Lit:
        return e;
    case expr_kind::MData:
        return whnf_core(mdata_expr(e));
    case expr_kind::FVar:
        return whnf_fvar(e);
    case expr_kind::App: case expr_kind::Let:
    case expr_kind::Proj:
        break;

    case expr_kind::Quote:
        return e;
    }

    // check cache
    if (m_memoize) {
        auto it = m_whnf_core_cache.find(e);
        if (it != m_whnf_core_cache.end())
            return it->second;
    }

    // do the actual work
    expr r;
    switch (e.kind()) {
    case expr_kind::BVar:  case expr_kind::Sort:  case expr_kind::MVar: case expr_kind::FVar:
    case expr_kind::Pi:    case expr_kind::Const: case expr_kind::Lambda:
    case expr_kind::Lit:   case expr_kind::MData:
        lean_unreachable(); // LCOV_EXCL_LINE

    case expr_kind::Quote:
        lean_unreachable();

    case expr_kind::Proj: {
        if (auto m = reduce_proj(e))
            r = whnf_core(*m);
        else
            r = e;
        break;
    }
    case expr_kind::App: {
        buffer<expr> args;
        expr f0 = get_app_rev_args(e, args);
        expr f = whnf_core(f0);
        if (is_lambda(f)) {
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            r = whnf_core(mk_rev_app(instantiate(binding_body(f), m, args.data() + (num_args - m)), num_args - m, args.data()));
        } else if (f == f0) {
            if (auto r = norm_ext(e)) {
                /* iota-reduction and quotient reduction rules */
                return whnf_core(*r);
            } else {
                return e;
            }
        } else {
            r = whnf_core(mk_rev_app(f, args.size(), args.data()));
        }
        break;
    }
    case expr_kind::Let:
        r = whnf_core(instantiate(let_body(e), let_value(e)));
        break;
    }

    if (m_memoize)
        m_whnf_core_cache.insert(mk_pair(e, r));
    return r;
}

/** \brief Return some definition \c d iff \c e is a target for delta-reduction, and the given definition is the one
    to be expanded. */
optional<declaration> type_checker::is_delta(expr const & e) const {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        if (auto d = m_env.find(const_name(f)))
            if (d->is_definition())
                return d;
    }
    return none_declaration();
}

optional<expr> type_checker::unfold_definition_core(expr const & e) {
    if (is_constant(e)) {
        if (auto d = is_delta(e)) {
            if (length(const_levels(e)) == d->get_num_univ_params())
                return some_expr(instantiate_value_univ_params(*d, const_levels(e)));
        }
    }
    return none_expr();
}

/* Unfold head(e) if it is a constant */
optional<expr> type_checker::unfold_definition(expr const & e) {
    if (is_app(e)) {
        expr f0 = get_app_fn(e);
        if (auto f  = unfold_definition_core(f0)) {
            buffer<expr> args;
            get_app_rev_args(e, args);
            return some_expr(mk_rev_app(*f, args));
        } else {
            return none_expr();
        }
    } else {
        return unfold_definition_core(e);
    }
}

/** \brief Put expression \c t in weak head normal form */
expr type_checker::whnf(expr const & e) {
    // Do not cache easy cases
    switch (e.kind()) {
    case expr_kind::BVar:  case expr_kind::Sort: case expr_kind::MVar: case expr_kind::Pi:
    case expr_kind::Lit:
        return e;
    case expr_kind::MData:
        return whnf(mdata_expr(e));
    case expr_kind::FVar:
        return whnf_fvar(e);
    case expr_kind::Lambda: case expr_kind::App:
    case expr_kind::Const:  case expr_kind::Let: case expr_kind::Proj:
        break;

    case expr_kind::Quote:
        return e;
    }

    // check cache
    if (m_memoize) {
        auto it = m_whnf_cache.find(e);
        if (it != m_whnf_cache.end())
            return it->second;
    }

    expr t = e;
    while (true) {
        expr t1 = whnf_core(t);
        if (auto next_t = unfold_definition(t1)) {
            t = *next_t;
        } else {
            auto r = t1;
            if (m_memoize)
                m_whnf_cache.insert(mk_pair(e, r));
            return r;
        }
    }
}

/** \brief Given lambda/Pi expressions \c t and \c s, return true iff \c t is def eq to \c s.

        t and s are definitionally equal
           iff
        domain(t) is definitionally equal to domain(s)
        and
        body(t) is definitionally equal to body(s) */
bool type_checker::is_def_eq_binding(expr t, expr s) {
    lean_assert(t.kind() == s.kind());
    lean_assert(is_binding(t));
    flet<local_ctx> save_lctx(m_lctx, m_lctx);
    expr_kind k = t.kind();
    buffer<expr> subst;
    do {
        optional<expr> var_s_type;
        if (binding_domain(t) != binding_domain(s)) {
            var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
            expr var_t_type = instantiate_rev(binding_domain(t), subst.size(), subst.data());
            if (!is_def_eq(var_t_type, *var_s_type))
                return false;
        }
        if (has_loose_bvars(binding_body(t)) || has_loose_bvars(binding_body(s))) {
            // free variable is used inside t or s
            if (!var_s_type)
                var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
            subst.push_back(m_lctx.mk_local_decl(m_name_generator, binding_name(s), *var_s_type, binding_info(s)));
        } else {
            subst.push_back(*g_dont_care); // don't care
        }
        t = binding_body(t);
        s = binding_body(s);
    } while (t.kind() == k && s.kind() == k);
    return is_def_eq(instantiate_rev(t, subst.size(), subst.data()),
                     instantiate_rev(s, subst.size(), subst.data()));
}

bool type_checker::is_def_eq(level const & l1, level const & l2) {
    if (is_equivalent(l1, l2)) {
        return true;
    } else {
        return false;
    }
}

bool type_checker::is_def_eq(levels const & ls1, levels const & ls2) {
    if (is_nil(ls1) && is_nil(ls2)) {
        return true;
    } else if (!is_nil(ls1) && !is_nil(ls2)) {
        return
            is_def_eq(head(ls1), head(ls2)) &&
            is_def_eq(tail(ls1), tail(ls2));
    } else {
        return false;
    }
}

/** \brief This is an auxiliary method for is_def_eq. It handles the "easy cases". */
lbool type_checker::quick_is_def_eq(expr const & t, expr const & s, bool use_hash) {
    if (m_eqv_manager.is_equiv(t, s, use_hash))
        return l_true;
    if (t.kind() == s.kind()) {
        switch (t.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return to_lbool(is_def_eq_binding(t, s));
        case expr_kind::Sort:
            return to_lbool(is_def_eq(sort_level(t), sort_level(s)));
        case expr_kind::MData:
            return to_lbool(is_def_eq(mdata_expr(t), mdata_expr(s)));
        case expr_kind::MVar:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::BVar:   case expr_kind::FVar: case expr_kind::App:
        case expr_kind::Const:  case expr_kind::Let:
        case expr_kind::Proj:
            // We do not handle these cases in this method.
            break;
        case expr_kind::Lit:
            return to_lbool(lit_value(t) == lit_value(s));

        case expr_kind::Quote:
            return to_lbool(t.raw() == s.raw());
        }
    }
    return l_undef; // This is not an "easy case"
}

/** \brief Return true if arguments of \c t are definitionally equal to arguments of \c s.
    This method is used to implement an optimization in the method \c is_def_eq. */
bool type_checker::is_def_eq_args(expr t, expr s) {
    while (is_app(t) && is_app(s)) {
        if (!is_def_eq(app_arg(t), app_arg(s)))
            return false;
        t = app_fn(t);
        s = app_fn(s);
    }
    return !is_app(t) && !is_app(s);
}

/** \brief Try to solve (fun (x : A), B) =?= s by trying eta-expansion on s */
bool type_checker::try_eta_expansion_core(expr const & t, expr const & s) {
    if (is_lambda(t) && !is_lambda(s)) {
        expr s_type = whnf(infer_type(s));
        if (!is_pi(s_type))
            return false;
        expr new_s  = mk_lambda(binding_name(s_type), binding_domain(s_type), mk_app(s, Var(0)), binding_info(s_type));
        if (!is_def_eq(t, new_s))
            return false;
        return true;
    } else {
        return false;
    }
}

/** \brief Return true if \c t and \c s are definitionally equal because they are applications of the form
    <tt>(f a_1 ... a_n)</tt> <tt>(g b_1 ... b_n)</tt>, and \c f and \c g are definitionally equal, and
    \c a_i and \c b_i are also definitionally equal for every 1 <= i <= n.
    Return false otherwise. */
bool type_checker::is_def_eq_app(expr const & t, expr const & s) {
    if (is_app(t) && is_app(s)) {
        buffer<expr> t_args;
        buffer<expr> s_args;
        expr t_fn = get_app_args(t, t_args);
        expr s_fn = get_app_args(s, s_args);
        if (is_def_eq(t_fn, s_fn) && t_args.size() == s_args.size()) {
            unsigned i = 0;
            for (; i < t_args.size(); i++) {
                if (!is_def_eq(t_args[i], s_args[i]))
                    break;
            }
            if (i == t_args.size())
                return true;
        }
    }
    return false;
}

/** \brief Return true if \c t and \c s are definitionally equal due to proof irrelevant.
    Return false otherwise. */
bool type_checker::is_def_eq_proof_irrel(expr const & t, expr const & s) {
    // Proof irrelevance support for Prop (aka Type.{0})
    expr t_type = infer_type(t);
    expr s_type = infer_type(s);
    return is_prop(t_type) && is_def_eq(t_type, s_type);
}

bool type_checker::failed_before(expr const & t, expr const & s) const {
    if (hash(t) < hash(s)) {
        return m_failure_cache.find(mk_pair(t, s)) != m_failure_cache.end();
    } else if (hash(t) > hash(s)) {
        return m_failure_cache.find(mk_pair(s, t)) != m_failure_cache.end();
    } else {
        return
            m_failure_cache.find(mk_pair(t, s)) != m_failure_cache.end() ||
            m_failure_cache.find(mk_pair(s, t)) != m_failure_cache.end();
    }
}

void type_checker::cache_failure(expr const & t, expr const & s) {
    if (hash(t) <= hash(s))
        m_failure_cache.insert(mk_pair(t, s));
    else
        m_failure_cache.insert(mk_pair(s, t));
}

static name * g_id_delta = nullptr;

/** \brief Perform one lazy delta-reduction step.
     Return
     - l_true if t_n and s_n are definitionally equal.
     - l_false if they are not definitionally equal.
     - l_undef it the step did not manage to establish whether they are definitionally equal or not.

     \remark t_n, s_n and cs are updated. */
auto type_checker::lazy_delta_reduction_step(expr & t_n, expr & s_n) -> reduction_status {
    auto d_t = is_delta(t_n);
    auto d_s = is_delta(s_n);
    if (!d_t && !d_s) {
        return reduction_status::DefUnknown;
    } else if (d_t && d_t->get_name() == *g_id_delta) {
        t_n = whnf_core(*unfold_definition(t_n));
        if (t_n == s_n)
            return reduction_status::DefEqual; /* id_delta t =?= t */
        if (auto u = unfold_definition(t_n))   /* id_delta t =?= s  ===>  unfold(t) =?= s */
            t_n = whnf_core(*u);
        return reduction_status::Continue;
    } else if (d_s && d_s->get_name() == *g_id_delta) {
        s_n = whnf_core(*unfold_definition(s_n));
        if (t_n == s_n)
            return reduction_status::DefEqual; /* t =?= id_delta t */
        if (auto u = unfold_definition(s_n))   /* t =?= id_delta s ===>  t =?= unfold(s) */
            s_n = whnf_core(*u);
        return reduction_status::Continue;
    } else if (d_t && !d_s) {
        t_n = whnf_core(*unfold_definition(t_n));
    } else if (!d_t && d_s) {
        s_n = whnf_core(*unfold_definition(s_n));
    } else {
        int c = compare(d_t->get_hints(), d_s->get_hints());
        if (c < 0) {
            t_n = whnf_core(*unfold_definition(t_n));
        } else if (c > 0) {
            s_n = whnf_core(*unfold_definition(s_n));
        } else {
            if (is_app(t_n) && is_app(s_n) && is_eqp(*d_t, *d_s)) {
                // If t_n and s_n are both applications of the same (non-opaque) definition,
                if (has_expr_metavar(t_n) || has_expr_metavar(s_n)) {
                    // We let the unifier deal with cases such as
                    // (f ...) =?= (f ...)
                    // when t_n or s_n contains metavariables
                    return reduction_status::DefUnknown;
                } else {
                    // Optimization:
                    // We try to check if their arguments are definitionally equal.
                    // If they are, then t_n and s_n must be definitionally equal, and we can
                    // skip the delta-reduction step.
                    // If the flag use_self_opt() is not true, then we skip this optimization
                    if (d_t->get_hints().use_self_opt() && !failed_before(t_n, s_n)) {
                        if (is_def_eq(const_levels(get_app_fn(t_n)), const_levels(get_app_fn(s_n))) &&
                            is_def_eq_args(t_n, s_n)) {
                            return reduction_status::DefEqual;
                        } else {
                            cache_failure(t_n, s_n);
                        }
                    }
                }
            }
            t_n = whnf_core(*unfold_definition(t_n));
            s_n = whnf_core(*unfold_definition(s_n));
        }
    }
    switch (quick_is_def_eq(t_n, s_n)) {
    case l_true:  return reduction_status::DefEqual;
    case l_false: return reduction_status::DefDiff;
    case l_undef: return reduction_status::Continue;
    }
    lean_unreachable();
}

lbool type_checker::lazy_delta_reduction(expr & t_n, expr & s_n) {
    while (true) {
        switch (lazy_delta_reduction_step(t_n, s_n)) {
        case reduction_status::Continue:   break;
        case reduction_status::DefUnknown: return l_undef;
        case reduction_status::DefEqual:   return l_true;
        case reduction_status::DefDiff:    return l_false;
        }
    }
}

bool type_checker::is_def_eq_core(expr const & t, expr const & s) {
    check_system("is_definitionally_equal");
    bool use_hash = true;
    lbool r = quick_is_def_eq(t, s, use_hash);
    if (r != l_undef) return r == l_true;

    // apply whnf (without using delta-reduction or normalizer extensions)
    expr t_n = whnf_core(t);
    expr s_n = whnf_core(s);

    if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
        r = quick_is_def_eq(t_n, s_n);
        if (r != l_undef) return r == l_true;
    }

    if (is_def_eq_proof_irrel(t_n, s_n))
        return true;

    r = lazy_delta_reduction(t_n, s_n);
    if (r != l_undef) return r == l_true;

    if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n) &&
        is_def_eq(const_levels(t_n), const_levels(s_n)))
        return true;

    if (is_fvar(t_n) && is_fvar(s_n) && fvar_name(t_n) == fvar_name(s_n))
        return true;

    if (is_proj(t_n) && is_proj(s_n) && proj_idx(t_n) == proj_idx(s_n) && is_def_eq(proj_expr(t_n), proj_expr(s_n)))
        return true;

    // At this point, t_n and s_n are in weak head normal form (modulo meta-variables and proof irrelevance)
    if (is_def_eq_app(t_n, s_n))
        return true;

    if (try_eta_expansion(t_n, s_n))
        return true;

    return false;
}

bool type_checker::is_def_eq(expr const & t, expr const & s) {
    bool r = is_def_eq_core(t, s);
    if (r)
        m_eqv_manager.add_equiv(t, s);
    return r;
}

type_checker::type_checker(environment const & env, local_ctx const & lctx, bool memoize, bool non_meta_only):
    m_env(env), m_lctx(lctx), m_name_generator(*g_kernel_fresh),
    m_memoize(memoize), m_non_meta_only(non_meta_only), m_params(nullptr) {
}

type_checker::~type_checker() {}

void check_no_metavar(environment const & env, name const & n, expr const & e) {
    if (has_metavar(e))
        throw declaration_has_metavars_exception(env, n, e);
}

static void check_no_fvar(environment const & env, name const & n, expr const & e) {
    if (has_fvar(e))
        throw declaration_has_free_vars_exception(env, n, e);
}

void check_no_metavar_no_fvar(environment const & env, name const & n, expr const & e) {
    check_no_metavar(env, n, e);
    check_no_fvar(env, n, e);
}

static void check_name(environment const & env, name const & n) {
    if (env.find(n))
        throw already_declared_exception(env, n);
}

static void check_duplicated_params(environment const & env, declaration const & d) {
    level_param_names ls = d.get_univ_params();
    while (!is_nil(ls)) {
        auto const & p = head(ls);
        ls = tail(ls);
        if (std::find(ls.begin(), ls.end(), p) != ls.end()) {
            throw kernel_exception(env, sstream() << "failed to add declaration to environment, "
                                   << "duplicate universe level parameter: '"
                                   << p << "'");
        }
    }
}

static void check_definition(environment const & env, declaration const & d, type_checker & checker) {
    check_no_metavar_no_fvar(env, d.get_name(), d.get_value());
    expr val_type = checker.check(d.get_value(), d.get_univ_params());
    if (!checker.is_def_eq(val_type, d.get_type())) {
        throw definition_type_mismatch_exception(env, d, val_type);
    }
}

static void check_decl_type(environment const & env, declaration const & d, type_checker & checker) {
    check_no_metavar_no_fvar(env, d.get_name(), d.get_type());
    check_name(env, d.get_name());
    check_duplicated_params(env, d);
    expr sort = checker.check(d.get_type(), d.get_univ_params());
    checker.ensure_sort(sort, d.get_type());
}

void check_decl_type(environment const & env, declaration const & d) {
    bool memoize = true; bool non_meta_only = !d.is_meta();
    type_checker checker(env, memoize, non_meta_only);
    check_decl_type(env, d, checker);
}

void check_decl_value(environment const & env, declaration const & d) {
    bool memoize = true; bool non_meta_only = !d.is_meta();
    type_checker checker(env, memoize, non_meta_only);
    if (d.is_definition()) {
        check_definition(env, d, checker);
    }
}

certified_declaration check(environment const & env, declaration const & d) {
    bool memoize = true; bool non_meta_only = !d.is_meta();
    type_checker checker(env, memoize, non_meta_only);
    check_decl_type(env, d, checker);
    if (d.is_definition()) {
        check_definition(env, d, checker);
    }
    return certified_declaration(env.get_id(), d);
}

certified_declaration certify_unchecked::certify(environment const & env, declaration const & d) {
    if (env.trust_lvl() == 0)
        throw kernel_exception(env, "environment trust level does not allow users to add declarations that were not type checked");
    return certified_declaration(env.get_id(), d);
}

certified_declaration certify_unchecked::certify_or_check(environment const & env, declaration const & d) {
    if (env.trust_lvl() == 0)
        return check(env, d);
    else
        return certify(env, d);
}

void initialize_type_checker() {
    g_id_delta     = new name("id_delta");
    g_dont_care    = new expr(Const("dontcare"));
    g_kernel_fresh = new name("_kernel_fresh");
    register_name_generator_prefix(*g_kernel_fresh);
}

void finalize_type_checker() {
    delete g_dont_care;
    delete g_id_delta;
    delete g_kernel_fresh;
}
}
