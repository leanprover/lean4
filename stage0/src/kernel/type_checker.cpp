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
#include "util/lbool.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/quot.h"
#include "kernel/inductive.h"

namespace lean {
static name * g_kernel_fresh = nullptr;
static expr * g_dont_care    = nullptr;
static expr * g_nat_zero     = nullptr;
static expr * g_nat_succ     = nullptr;
static expr * g_nat_add      = nullptr;
static expr * g_nat_sub      = nullptr;
static expr * g_nat_mul      = nullptr;
static expr * g_nat_mod      = nullptr;
static expr * g_nat_div      = nullptr;
static expr * g_nat_beq      = nullptr;
static expr * g_nat_ble      = nullptr;

type_checker::state::state(environment const & env):
    m_env(env), m_ngen(*g_kernel_fresh) {}

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
        throw type_expected_exception(env(), m_lctx, s);
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
        throw function_expected_exception(env(), m_lctx, s);
    }
}

void type_checker::check_level(level const & l) {
    if (m_lparams) {
        if (auto n2 = get_undef_param(l, *m_lparams))
            throw kernel_exception(env(), sstream() << "invalid reference to undefined universe level parameter '"
                                   << *n2 << "'");
    }
}

expr type_checker::infer_fvar(expr const & e) {
    if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
        return decl->get_type();
    } else {
        throw kernel_exception(env(), "unknown free variable");
    }
}

expr type_checker::infer_constant(expr const & e, bool infer_only) {
    constant_info info = env().get(const_name(e));
    auto const & ps = info.get_lparams();
    auto const & ls = const_levels(e);
    if (length(ps) != length(ls))
        throw kernel_exception(env(), sstream() << "incorrect number of universe levels parameters for '"
                               << const_name(e) << "', #"
                               << length(ps)  << " expected, #" << length(ls) << " provided");
    if (!infer_only) {
        if (m_safe_only && info.is_unsafe()) {
            throw kernel_exception(env(), sstream() << "invalid declaration, it uses unsafe declaration '"
                                   << const_name(e) << "'");
        }
        for (level const & l : ls)
            check_level(l);
    }
    return instantiate_type_lparams(info, ls);
}

expr type_checker::infer_lambda(expr const & _e, bool infer_only) {
    flet<local_ctx> save_lctx(m_lctx, m_lctx);
    buffer<expr> fvars;
    expr e = _e;
    while (is_lambda(e)) {
        expr d    = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
        expr fvar = m_lctx.mk_local_decl(m_st->m_ngen, binding_name(e), d, binding_info(e));
        fvars.push_back(fvar);
        if (!infer_only) {
            ensure_sort_core(infer_type_core(d, infer_only), d);
        }
        e = binding_body(e);
    }
    expr r = infer_type_core(instantiate_rev(e, fvars.size(), fvars.data()), infer_only);
    r = cheap_beta_reduce(r);
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
        expr fvar  = m_lctx.mk_local_decl(m_st->m_ngen, binding_name(e), d, binding_info(e));
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
            throw app_type_mismatch_exception(env(), m_lctx, e, f_type, a_type);
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

static void mark_used(unsigned n, expr const * fvars, expr const & b, bool * used) {
    if (!has_fvar(b)) return;
    for_each(b, [&](expr const & x, unsigned) {
            if (!has_fvar(x)) return false;
            if (is_fvar(x)) {
                for (unsigned i = 0; i < n; i++) {
                    if (fvar_name(fvars[i]) == fvar_name(x)) {
                        used[i] = true;
                        return false;
                    }
                }
            }
            return true;
        });
}

expr type_checker::infer_let(expr const & _e, bool infer_only) {
    flet<local_ctx> save_lctx(m_lctx, m_lctx);
    buffer<expr> fvars;
    buffer<expr> vals;
    expr e = _e;
    while (is_let(e)) {
        expr type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
        expr val  = instantiate_rev(let_value(e), fvars.size(), fvars.data());
        expr fvar = m_lctx.mk_local_decl(m_st->m_ngen, let_name(e), type, val);
        fvars.push_back(fvar);
        vals.push_back(val);
        if (!infer_only) {
            ensure_sort_core(infer_type_core(type, infer_only), type);
            expr val_type = infer_type_core(val, infer_only);
            if (!is_def_eq(val_type, type)) {
                throw def_type_mismatch_exception(env(), m_lctx, let_name(e), val_type, type);
            }
        }
        e = let_body(e);
    }
    expr r = infer_type_core(instantiate_rev(e, fvars.size(), fvars.data()), infer_only);
    r = cheap_beta_reduce(r); // use `cheap_beta_reduce` (to try) to reduce number of dependencies
    buffer<bool, 128> used;
    used.resize(fvars.size(), false);
    mark_used(fvars.size(), fvars.data(), r, used.data());
    unsigned i = fvars.size();
    while (i > 0) {
        --i;
        if (used[i])
            mark_used(i, fvars.data(), vals[i], used.data());
    }
    buffer<expr> used_fvars;
    for (unsigned i = 0; i < fvars.size(); i++) {
        if (used[i])
            used_fvars.push_back(fvars[i]);
    }
    return m_lctx.mk_pi(used_fvars, r);
}

expr type_checker::infer_proj(expr const & e, bool infer_only) {
    expr type = whnf(infer_type_core(proj_expr(e), infer_only));
    if (!proj_idx(e).is_small())
        throw invalid_proj_exception(env(), m_lctx, e);
    unsigned idx = proj_idx(e).get_small_value();
    buffer<expr> args;
    expr const & I = get_app_args(type, args);
    if (!is_constant(I))
        throw invalid_proj_exception(env(), m_lctx, e);
    name const & I_name  = const_name(I);
    if (I_name != proj_sname(e))
        throw invalid_proj_exception(env(), m_lctx, e);
    constant_info I_info = env().get(I_name);
    if (!I_info.is_inductive())
        throw invalid_proj_exception(env(), m_lctx, e);
    inductive_val I_val = I_info.to_inductive_val();
    if (length(I_val.get_cnstrs()) != 1 || args.size() != I_val.get_nparams() + I_val.get_nindices())
        throw invalid_proj_exception(env(), m_lctx, e);

    constant_info c_info = env().get(head(I_val.get_cnstrs()));
    expr r = instantiate_type_lparams(c_info, const_levels(I));
    for (unsigned i = 0; i < I_val.get_nparams(); i++) {
        lean_assert(i < args.size());
        r = whnf(r);
        if (!is_pi(r)) throw invalid_proj_exception(env(), m_lctx, e);
        r = instantiate(binding_body(r), args[i]);
    }
    for (unsigned i = 0; i < idx; i++) {
        r = whnf(r);
        if (!is_pi(r)) throw invalid_proj_exception(env(), m_lctx, e);
        if (has_loose_bvars(binding_body(r)))
            r = instantiate(binding_body(r), mk_proj(I_name, i, proj_expr(e)));
        else
            r = binding_body(r);
    }
    r = whnf(r);
    if (!is_pi(r)) throw invalid_proj_exception(env(), m_lctx, e);
    return binding_domain(r);
}

/** \brief Return type of expression \c e, if \c infer_only is false, then it also check whether \c e is type correct or not.
    \pre closed(e) */
expr type_checker::infer_type_core(expr const & e, bool infer_only) {
    if (is_bvar(e))
        throw kernel_exception(env(), "type checker does not support loose bound variables, replace them with free variables before invoking it");

    lean_assert(!has_loose_bvars(e));
    check_system("type checker");

    auto it = m_st->m_infer_type[infer_only].find(e);
    if (it != m_st->m_infer_type[infer_only].end())
        return it->second;

    expr r;
    switch (e.kind()) {
    case expr_kind::Lit:      r = lit_type(lit_value(e)); break;
    case expr_kind::MData:    r = infer_type_core(mdata_expr(e), infer_only); break;
    case expr_kind::Proj:     r = infer_proj(e, infer_only); break;
    case expr_kind::FVar:     r = infer_fvar(e);  break;
    case expr_kind::MVar:     throw kernel_exception(env(), "kernel type checker does not support meta variables");
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
    }

    m_st->m_infer_type[infer_only].insert(mk_pair(e, r));
    return r;
}

expr type_checker::infer_type(expr const & e) {
    return infer_type_core(e, true);
}

expr type_checker::check(expr const & e, names const & lps) {
    flet<names const *> updt(m_lparams, &lps);
    return infer_type_core(e, false);
}

expr type_checker::check_ignore_undefined_universes(expr const & e) {
    flet<names const *> updt(m_lparams, nullptr);
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

/** \brief Apply normalizer extensions to \c e.
    If `cheap == true`, then we don't perform delta-reduction when reducing major premise. */
optional<expr> type_checker::reduce_recursor(expr const & e, bool cheap) {
    if (env().is_quot_initialized()) {
        if (optional<expr> r = quot_reduce_rec(e, [&](expr const & e) { return whnf(e); })) {
            return r;
        }
    }
    if (optional<expr> r = inductive_reduce_rec(env(), e,
                                                [&](expr const & e) { return cheap ? whnf_core(e, cheap) : whnf(e); },
                                                [&](expr const & e) { return infer(e); },
                                                [&](expr const & e1, expr const & e2) { return is_def_eq(e1, e2); })) {
        return r;
    }
    return none_expr();
}

expr type_checker::whnf_fvar(expr const & e, bool cheap) {
    if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
        if (optional<expr> const & v = decl->get_value()) {
            /* zeta-reduction */
            return whnf_core(*v, cheap);
        }
    }
    return e;
}

/* If `cheap == true`, then we don't perform delta-reduction when reducing major premise. */
optional<expr> type_checker::reduce_proj(expr const & e, bool cheap) {
    if (!proj_idx(e).is_small())
        return none_expr();
    unsigned idx = proj_idx(e).get_small_value();
    expr c;
    if (cheap)
        c = whnf_core(proj_expr(e), cheap);
    else
        c = whnf(proj_expr(e));
    if (is_string_lit(c))
        c = string_lit_to_constructor(c);
    buffer<expr> args;
    expr const & mk = get_app_args(c, args);
    if (!is_constant(mk))
        return none_expr();
    constant_info mk_info = env().get(const_name(mk));
    if (!mk_info.is_constructor())
        return none_expr();
    unsigned nparams = mk_info.to_constructor_val().get_nparams();
    if (nparams + idx < args.size())
        return some_expr(args[nparams + idx]);
    else
        return none_expr();
}

static bool is_let_fvar(local_ctx const & lctx, expr const & e) {
    lean_assert(is_fvar(e));
    if (optional<local_decl> decl = lctx.find_local_decl(e)) {
        return static_cast<bool>(decl->get_value());
    } else {
        return false;
    }
}

/** \brief Weak head normal form core procedure. It does not perform delta reduction nor normalization extensions.
    If `cheap == true`, then we don't perform delta-reduction when reducing major premise of recursors and projections.
    We also do not cache results. */
expr type_checker::whnf_core(expr const & e, bool cheap) {
    check_system("whnf");

    // handle easy cases
    switch (e.kind()) {
    case expr_kind::BVar: case expr_kind::Sort:  case expr_kind::MVar:
    case expr_kind::Pi:   case expr_kind::Const: case expr_kind::Lambda:
    case expr_kind::Lit:
        return e;
    case expr_kind::MData:
        return whnf_core(mdata_expr(e), cheap);
    case expr_kind::FVar:
        if (is_let_fvar(m_lctx, e))
            break;
        else
            return e;
    case expr_kind::App: case expr_kind::Let:
    case expr_kind::Proj:
        break;
    }

    // check cache
    if (!cheap) {
        auto it = m_st->m_whnf_core.find(e);
        if (it != m_st->m_whnf_core.end())
            return it->second;
    }

    // do the actual work
    expr r;
    switch (e.kind()) {
    case expr_kind::BVar:  case expr_kind::Sort:  case expr_kind::MVar:
    case expr_kind::Pi:    case expr_kind::Const: case expr_kind::Lambda:
    case expr_kind::Lit:   case expr_kind::MData:
        lean_unreachable(); // LCOV_EXCL_LINE
    case expr_kind::FVar:
        return whnf_fvar(e, cheap);
    case expr_kind::Proj: {
        if (auto m = reduce_proj(e, cheap))
            r = whnf_core(*m, cheap);
        else
            r = e;
        break;
    }
    case expr_kind::App: {
        buffer<expr> args;
        expr f0 = get_app_rev_args(e, args);
        expr f = whnf_core(f0, cheap);
        if (is_lambda(f)) {
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            r = whnf_core(mk_rev_app(instantiate(binding_body(f), m, args.data() + (num_args - m)), num_args - m, args.data()), cheap);
        } else if (f == f0) {
            if (auto r = reduce_recursor(e, cheap)) {
                /* iota-reduction and quotient reduction rules */
                return whnf_core(*r, cheap);
            } else {
                return e;
            }
        } else {
            r = whnf_core(mk_rev_app(f, args.size(), args.data()), cheap);
        }
        break;
    }
    case expr_kind::Let:
        r = whnf_core(instantiate(let_body(e), let_value(e)), cheap);
        break;
    }

    if (!cheap) {
        m_st->m_whnf_core.insert(mk_pair(e, r));
    }
    return r;
}

/** \brief Return some definition \c d iff \c e is a target for delta-reduction, and the given definition is the one
    to be expanded. */
optional<constant_info> type_checker::is_delta(expr const & e) const {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        if (optional<constant_info> info = env().find(const_name(f)))
            if (info->has_value())
                return info;
    }
    return none_constant_info();
}

optional<expr> type_checker::unfold_definition_core(expr const & e) {
    if (is_constant(e)) {
        if (auto d = is_delta(e)) {
            if (length(const_levels(e)) == d->get_num_lparams())
                return some_expr(instantiate_value_lparams(*d, const_levels(e)));
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

static expr * g_lean_reduce_bool = nullptr;
static expr * g_lean_reduce_nat  = nullptr;

namespace ir {
object * run_boxed(environment const & env, options const & opts, name const & fn, unsigned n, object **args);
}

expr mk_bool_true();
expr mk_bool_false();

optional<expr> reduce_native(environment const & env, expr const & e) {
    if (!is_app(e)) return none_expr();
    expr const & arg = app_arg(e);
    if (!is_constant(arg)) return none_expr();
    if (app_fn(e) == *g_lean_reduce_bool) {
        object * r = ir::run_boxed(env, options(), const_name(arg), 0, nullptr);
        if (!lean_is_scalar(r)) {
            lean_dec_ref(r);
            throw kernel_exception(env, "type checker failure, unexpected result value for 'Lean.reduceBool'");
        }
        return lean_unbox(r) == 0 ? some_expr(mk_bool_false()) : some_expr(mk_bool_true());
    }
    if (app_fn(e) == *g_lean_reduce_nat) {
        object * r = ir::run_boxed(env, options(), const_name(arg), 0, nullptr);
        if (lean_is_scalar(r) || lean_is_mpz(r)) {
            return some_expr(mk_lit(literal(nat(r))));
        } else {
            throw kernel_exception(env, "type checker failure, unexpected result value for 'Lean.reduceNat'");
        }
    }
    return none_expr();
}

static inline bool is_nat_lit_ext(expr const & e) { return e == *g_nat_zero || is_nat_lit(e); }
static inline nat get_nat_val(expr const & e) {
    lean_assert(is_nat_lit_ext(e));
    if (e == *g_nat_zero) return nat((unsigned)0);
    return lit_value(e).get_nat();
}

template<typename F> optional<expr> type_checker::reduce_bin_nat_op(F const & f, expr const & e) {
    expr arg1 = whnf(app_arg(app_fn(e)));
    if (!is_nat_lit_ext(arg1)) return none_expr();
    expr arg2 = whnf(app_arg(e));
    if (!is_nat_lit_ext(arg2)) return none_expr();
    nat v1 = get_nat_val(arg1);
    nat v2 = get_nat_val(arg2);
    return some_expr(mk_lit(literal(nat(f(v1.raw(), v2.raw())))));
}

template<typename F> optional<expr> type_checker::reduce_bin_nat_pred(F const & f, expr const & e) {
    expr arg1 = whnf(app_arg(app_fn(e)));
    if (!is_nat_lit_ext(arg1)) return none_expr();
    expr arg2 = whnf(app_arg(e));
    if (!is_nat_lit_ext(arg2)) return none_expr();
    nat v1 = get_nat_val(arg1);
    nat v2 = get_nat_val(arg2);
    return f(v1.raw(), v2.raw()) ? some_expr(mk_bool_true()) : some_expr(mk_bool_false());
}

optional<expr> type_checker::reduce_nat(expr const & e) {
    if (has_fvar(e)) return none_expr();
    unsigned nargs = get_app_num_args(e);
    if (nargs == 1) {
        expr const & f = app_fn(e);
        if (f == *g_nat_succ) {
            expr arg = whnf(app_arg(e));
            if (!is_nat_lit_ext(arg)) return none_expr();
            nat v = get_nat_val(arg);
            return some_expr(mk_lit(literal(nat(v+nat(1)))));
        }
    } else if (nargs == 2) {
        expr const & f = app_fn(app_fn(e));
        if (!is_constant(f)) return none_expr();
        if (f == *g_nat_add) return reduce_bin_nat_op(nat_add, e);
        if (f == *g_nat_sub) return reduce_bin_nat_op(nat_sub, e);
        if (f == *g_nat_mul) return reduce_bin_nat_op(nat_mul, e);
        if (f == *g_nat_mod) return reduce_bin_nat_op(nat_mod, e);
        if (f == *g_nat_div) return reduce_bin_nat_op(nat_div, e);
        if (f == *g_nat_beq) return reduce_bin_nat_pred(nat_eq, e);
        if (f == *g_nat_ble) return reduce_bin_nat_pred(nat_le, e);
    }
    return none_expr();
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
        if (is_let_fvar(m_lctx, e))
            break;
        else
            return e;
    case expr_kind::Lambda: case expr_kind::App:
    case expr_kind::Const:  case expr_kind::Let: case expr_kind::Proj:
        break;
    }

    // check cache
    auto it = m_st->m_whnf.find(e);
    if (it != m_st->m_whnf.end())
        return it->second;

    expr t = e;
    while (true) {
        expr t1 = whnf_core(t);
        if (auto v = reduce_native(env(), t1)) {
            m_st->m_whnf.insert(mk_pair(e, *v));
            return *v;
        } else if (auto v = reduce_nat(t1)) {
            m_st->m_whnf.insert(mk_pair(e, *v));
            return *v;
        } else if (auto next_t = unfold_definition(t1)) {
            t = *next_t;
        } else {
            auto r = t1;
            m_st->m_whnf.insert(mk_pair(e, r));
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
            subst.push_back(m_lctx.mk_local_decl(m_st->m_ngen, binding_name(s), *var_s_type, binding_info(s)));
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
    if (m_st->m_eqv_manager.is_equiv(t, s, use_hash))
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
        expr new_s  = mk_lambda(binding_name(s_type), binding_domain(s_type), mk_app(s, mk_bvar(0)), binding_info(s_type));
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
lbool type_checker::is_def_eq_proof_irrel(expr const & t, expr const & s) {
    // Proof irrelevance support for Prop (aka Type.{0})
    expr t_type = infer_type(t);
    if (!is_prop(t_type))
        return l_undef;
    expr s_type = infer_type(s);
    return to_lbool(is_def_eq(t_type, s_type));
}

bool type_checker::failed_before(expr const & t, expr const & s) const {
    if (hash(t) < hash(s)) {
        return m_st->m_failure.find(mk_pair(t, s)) != m_st->m_failure.end();
    } else if (hash(t) > hash(s)) {
        return m_st->m_failure.find(mk_pair(s, t)) != m_st->m_failure.end();
    } else {
        return
            m_st->m_failure.find(mk_pair(t, s)) != m_st->m_failure.end() ||
            m_st->m_failure.find(mk_pair(s, t)) != m_st->m_failure.end();
    }
}

void type_checker::cache_failure(expr const & t, expr const & s) {
    if (hash(t) <= hash(s))
        m_st->m_failure.insert(mk_pair(t, s));
    else
        m_st->m_failure.insert(mk_pair(s, t));
}

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
            if (is_app(t_n) && is_app(s_n) && is_eqp(*d_t, *d_s) && d_t->get_hints().is_regular()) {
                // Optimization:
                // We try to check if their arguments are definitionally equal.
                // If they are, then t_n and s_n must be definitionally equal, and we can
                // skip the delta-reduction step.
                if (!failed_before(t_n, s_n)) {
                    if (is_def_eq(const_levels(get_app_fn(t_n)), const_levels(get_app_fn(s_n))) &&
                        is_def_eq_args(t_n, s_n)) {
                        return reduction_status::DefEqual;
                    } else {
                        cache_failure(t_n, s_n);
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

inline bool is_nat_zero(expr const & t) {
    return t == *g_nat_zero || (is_nat_lit(t) && lit_value(t).is_zero());
}

inline optional<expr> is_nat_succ(expr const & t) {
    if (is_nat_lit(t)) {
        nat val = lit_value(t).get_nat();
        if (!val.is_zero()) {
            return some_expr(mk_lit(literal(val - nat(1))));
        }
    }

    if (get_app_fn(t) == *g_nat_succ && get_app_num_args(t) == 1) {
        return some_expr(app_arg(t));
    }
    return none_expr();
}

lbool type_checker::is_def_eq_offset(expr const & t, expr const & s) {
    if (is_nat_zero(t) && is_nat_zero(s))
        return l_true;
    optional<expr> pred_t = is_nat_succ(t);
    optional<expr> pred_s = is_nat_succ(s);
    if (pred_t && pred_s) {
        return to_lbool(is_def_eq_core(*pred_t, *pred_s));
    }
    return l_undef;
}

lbool type_checker::lazy_delta_reduction(expr & t_n, expr & s_n) {
    while (true) {
        lbool r = is_def_eq_offset(t_n, s_n);
        if (r != l_undef) return r;

        if (!has_fvar(t_n) && !has_fvar(s_n)) {
            if (auto t_v = reduce_nat(t_n)) {
                return to_lbool(is_def_eq_core(*t_v, s_n));
            } else if (auto s_v = reduce_nat(s_n)) {
                return to_lbool(is_def_eq_core(t_n, *s_v));
            }
        }

        if (auto t_v = reduce_native(env(), t_n)) {
            return to_lbool(is_def_eq_core(*t_v, s_n));
        } else if (auto s_v = reduce_native(env(), s_n)) {
            return to_lbool(is_def_eq_core(t_n, *s_v));
        }

        switch (lazy_delta_reduction_step(t_n, s_n)) {
        case reduction_status::Continue:   break;
        case reduction_status::DefUnknown: return l_undef;
        case reduction_status::DefEqual:   return l_true;
        case reduction_status::DefDiff:    return l_false;
        }
    }
}

static expr * g_string_mk = nullptr;

lbool type_checker::try_string_lit_expansion_core(expr const & t, expr const & s) {
    if (is_string_lit(t) && is_app(s) && app_fn(s) == *g_string_mk) {
        return to_lbool(is_def_eq_core(string_lit_to_constructor(t), s));
    }
    return l_undef;
}

lbool type_checker::try_string_lit_expansion(expr const & t, expr const & s) {
    lbool r = try_string_lit_expansion_core(t, s);
    if (r != l_undef) return r;
    return try_string_lit_expansion_core(s, t);
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

    r = is_def_eq_proof_irrel(t_n, s_n);
    if (r != l_undef) return r == l_true;

    r = lazy_delta_reduction(t_n, s_n);
    if (r != l_undef) return r == l_true;

    if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n) &&
        is_def_eq(const_levels(t_n), const_levels(s_n)))
        return true;

    if (is_fvar(t_n) && is_fvar(s_n) && fvar_name(t_n) == fvar_name(s_n))
        return true;

    if (is_proj(t_n) && is_proj(s_n) && proj_idx(t_n) == proj_idx(s_n) && is_def_eq(proj_expr(t_n), proj_expr(s_n)))
        return true;

    // At this point, t_n and s_n are in weak head normal form (modulo metavariables and proof irrelevance)
    if (is_def_eq_app(t_n, s_n))
        return true;

    if (try_eta_expansion(t_n, s_n))
        return true;

    r = try_string_lit_expansion(t_n, s_n);
    if (r != l_undef) return r == l_true;

    return false;
}

bool type_checker::is_def_eq(expr const & t, expr const & s) {
    bool r = is_def_eq_core(t, s);
    if (r)
        m_st->m_eqv_manager.add_equiv(t, s);
    return r;
}

expr type_checker::eta_expand(expr const & e) {
    buffer<expr> fvars;
    flet<local_ctx> save_lctx(m_lctx, m_lctx);
    expr it = e;
    while (is_lambda(it)) {
        expr d = instantiate_rev(binding_domain(it), fvars.size(), fvars.data());
        fvars.push_back(m_lctx.mk_local_decl(m_st->m_ngen, binding_name(it), d, binding_info(it)));
        it     = binding_body(it);
    }
    it = instantiate_rev(it, fvars.size(), fvars.data());
    expr it_type = whnf(infer(it));
    if (!is_pi(it_type)) return e;
    buffer<expr> args;
    while (is_pi(it_type)) {
        expr arg = m_lctx.mk_local_decl(m_st->m_ngen, binding_name(it_type), binding_domain(it_type), binding_info(it_type));
        args.push_back(arg);
        fvars.push_back(arg);
        it_type  = whnf(instantiate(binding_body(it_type), arg));
    }
    expr r = mk_app(it, args);
    return m_lctx.mk_lambda(fvars, r);
}

type_checker::type_checker(environment const & env, local_ctx const & lctx, bool safe_only):
    m_st_owner(true), m_st(new state(env)),
    m_lctx(lctx), m_safe_only(safe_only), m_lparams(nullptr) {
}

type_checker::type_checker(state & st, local_ctx const & lctx, bool safe_only):
    m_st_owner(false), m_st(&st), m_lctx(lctx),
    m_safe_only(safe_only), m_lparams(nullptr) {
}

type_checker::type_checker(type_checker && src):
    m_st_owner(src.m_st_owner), m_st(src.m_st), m_lctx(std::move(src.m_lctx)),
    m_safe_only(src.m_safe_only), m_lparams(src.m_lparams) {
    src.m_st_owner = false;
}

type_checker::~type_checker() {
    if (m_st_owner)
        delete m_st;
}

extern "C" LEAN_EXPORT uint8 lean_kernel_is_def_eq(lean_object * env, lean_object * lctx, lean_object * a, lean_object * b) {
    return type_checker(environment(env), local_ctx(lctx)).is_def_eq(expr(a), expr(b));
}

extern "C" LEAN_EXPORT lean_object * lean_kernel_whnf(lean_object * env, lean_object * lctx, lean_object * a) {
    return type_checker(environment(env), local_ctx(lctx)).whnf(expr(a)).steal();
}

void initialize_type_checker() {
    g_dont_care    = new expr(mk_const("dontcare"));
    mark_persistent(g_dont_care->raw());
    g_kernel_fresh = new name("_kernel_fresh");
    mark_persistent(g_kernel_fresh->raw());
    g_nat_zero     = new expr(mk_constant(name{"Nat", "zero"}));
    mark_persistent(g_nat_zero->raw());
    g_nat_succ     = new expr(mk_constant(name{"Nat", "succ"}));
    mark_persistent(g_nat_succ->raw());
    g_nat_add      = new expr(mk_constant(name{"Nat", "add"}));
    mark_persistent(g_nat_add->raw());
    g_nat_sub      = new expr(mk_constant(name{"Nat", "sub"}));
    mark_persistent(g_nat_sub->raw());
    g_nat_mul      = new expr(mk_constant(name{"Nat", "mul"}));
    mark_persistent(g_nat_mul->raw());
    g_nat_div      = new expr(mk_constant(name{"Nat", "div"}));
    mark_persistent(g_nat_div->raw());
    g_nat_mod      = new expr(mk_constant(name{"Nat", "mod"}));
    mark_persistent(g_nat_mod->raw());
    g_nat_beq      = new expr(mk_constant(name{"Nat", "beq"}));
    mark_persistent(g_nat_beq->raw());
    g_nat_ble      = new expr(mk_constant(name{"Nat", "ble"}));
    mark_persistent(g_nat_ble->raw());
    g_string_mk    = new expr(mk_constant(name{"String", "mk"}));
    mark_persistent(g_string_mk->raw());
    g_lean_reduce_bool = new expr(mk_constant(name{"Lean", "reduceBool"}));
    mark_persistent(g_lean_reduce_bool->raw());
    g_lean_reduce_nat  = new expr(mk_constant(name{"Lean", "reduceNat"}));
    mark_persistent(g_lean_reduce_nat->raw());
    register_name_generator_prefix(*g_kernel_fresh);
}

void finalize_type_checker() {
    delete g_dont_care;
    delete g_kernel_fresh;
    delete g_nat_succ;
    delete g_nat_zero;
    delete g_nat_add;
    delete g_nat_sub;
    delete g_nat_mul;
    delete g_nat_div;
    delete g_nat_mod;
    delete g_nat_beq;
    delete g_nat_ble;
    delete g_string_mk;
    delete g_lean_reduce_bool;
    delete g_lean_reduce_nat;
}
}
