/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <algorithm>
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/projection.h"
#include "library/normalize.h"
#include "library/replace_visitor.h"
#include "library/type_context.h"
#include "library/pp_options.h"
#include "library/reducible.h"
#include "library/generic_exception.h"
#include "library/class.h"

#ifndef LEAN_DEFAULT_CLASS_TRACE_INSTANCES
#define LEAN_DEFAULT_CLASS_TRACE_INSTANCES false
#endif

#ifndef LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH
#define LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH 32
#endif

#ifndef LEAN_DEFAULT_CLASS_TRANS_INSTANCES
#define LEAN_DEFAULT_CLASS_TRANS_INSTANCES true
#endif

namespace lean {
static name * g_prefix                       = nullptr;
static name * g_class_trace_instances        = nullptr;
static name * g_class_instance_max_depth     = nullptr;
static name * g_class_trans_instances        = nullptr;

bool get_class_trace_instances(options const & o) {
    return o.get_bool(*g_class_trace_instances, LEAN_DEFAULT_CLASS_TRACE_INSTANCES);
}

unsigned get_class_instance_max_depth(options const & o) {
    return o.get_unsigned(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH);
}

bool get_class_trans_instances(options const & o) {
    return o.get_bool(*g_class_trans_instances, LEAN_DEFAULT_CLASS_TRANS_INSTANCES);
}

struct type_context::ext_ctx : public extension_context {
    type_context & m_owner;

    ext_ctx(type_context & o):m_owner(o) {}

    virtual environment const & env() const { return m_owner.m_env; }

    virtual pair<expr, constraint_seq> whnf(expr const & e) {
        return mk_pair(m_owner.whnf(e), constraint_seq());
    }

    virtual pair<bool, constraint_seq> is_def_eq(expr const & e1, expr const & e2, delayed_justification &) {
        return mk_pair(m_owner.is_def_eq(e1, e2), constraint_seq());
    }

    virtual pair<expr, constraint_seq> check_type(expr const & e, bool) {
        return mk_pair(m_owner.infer(e), constraint_seq());
    }

    virtual name mk_fresh_name() {
        return m_owner.m_ngen.next();
    }

    virtual optional<expr> is_stuck(expr const &) {
        return none_expr();
    }
};

type_context::type_context(environment const & env, io_state const & ios, bool multiple_instances):
    m_env(env),
    m_ios(ios),
    m_ngen(*g_prefix),
    m_ext_ctx(new ext_ctx(*this)),
    m_proj_info(get_projection_info_map(env)) {
    m_pip                   = nullptr;
    m_ci_multiple_instances = multiple_instances;
    m_ignore_external_mvars = false;
    m_check_types           = true;
    // TODO(Leo): use compilation options for setting config
    m_ci_max_depth       = 32;
    m_ci_trans_instances = true;
    m_ci_trace_instances = false;
    update_options(ios.get_options());
}

type_context::~type_context() {
}

void type_context::set_context(list<expr> const & ctx) {
    clear_cache();
    m_ci_local_instances.clear();
    for (expr const & e : ctx) {
        if (auto cname = is_class(infer(e))) {
            m_ci_local_instances.push_back(mk_pair(*cname, e));
        }
    }
}

bool type_context::is_opaque(declaration const & d) const {
    if (d.is_theorem())
        return true;
    name const & n = d.get_name();
    return m_proj_info.contains(n) || is_extra_opaque(n);
}

optional<expr> type_context::expand_macro(expr const & m) {
    lean_assert(is_macro(m));
    return macro_def(m).expand(m, *m_ext_ctx);
}

optional<expr> type_context::reduce_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    projection_info const * info = m_proj_info.find(const_name(f));
    if (!info)
        return none_expr();
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= info->m_nparams)
        return none_expr();
    unsigned mkidx  = info->m_nparams;
    expr const & mk = args[mkidx];
    expr new_mk     = whnf(mk);
    expr const & new_mk_fn = get_app_fn(new_mk);
    if (!is_constant(new_mk_fn) || const_name(new_mk_fn) != info->m_constructor)
        return none_expr();
    buffer<expr> mk_args;
    get_app_args(new_mk, mk_args);
    unsigned i = info->m_nparams + info->m_i;
    if (i >= mk_args.size())
        none_expr();
    expr r = mk_args[i];
    r = mk_app(r, args.size() - mkidx - 1, args.data() + mkidx + 1);
    return some_expr(r);
}

optional<expr> type_context::norm_ext(expr const & e) {
    if (auto r = reduce_projection(e)) {
        return r;
    } else if (auto r = m_env.norm_ext()(e, *m_ext_ctx)) {
        return some_expr(r->first);
    } else {
        return none_expr();
    }
}

expr type_context::whnf_core(expr const & e) {
    check_system("whnf");
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
    case expr_kind::Pi:  case expr_kind::Constant: case expr_kind::Lambda:
        return e;
    case expr_kind::Macro:
        if (auto m = expand_macro(e))
            return whnf_core(*m);
        else
            return e;
        break;
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
            return whnf_core(mk_rev_app(instantiate(binding_body(f), m, args.data() + (num_args - m)),
                                        num_args - m, args.data()));
        } else {
            return f == f0 ? e : whnf_core(mk_rev_app(f, args.size(), args.data()));
        }
    }}
    lean_unreachable();
}

/** \brief Expand \c e if it is non-opaque constant with height >= h */
expr type_context::unfold_name_core(expr e, unsigned h) {
    if (is_constant(e)) {
        if (auto d = m_env.find(const_name(e))) {
            if (d->is_definition() && !is_opaque(*d) && d->get_height() >= h &&
                length(const_levels(e)) == d->get_num_univ_params())
                return unfold_name_core(instantiate_value_univ_params(*d, const_levels(e)), h);
        }
    }
    return e;
}

/** \brief Expand constants and application where the function is a constant.
    The unfolding is only performend if the constant corresponds to
    a non-opaque definition with height >= h */
expr type_context::unfold_names(expr const & e, unsigned h) {
    if (is_app(e)) {
        expr f0 = get_app_fn(e);
        expr f  = unfold_name_core(f0, h);
        if (is_eqp(f, f0)) {
            return e;
        } else {
            buffer<expr> args;
            get_app_rev_args(e, args);
            return mk_rev_app(f, args);
        }
    } else {
        return unfold_name_core(e, h);
    }
}

/** \brief Return some definition \c d iff \c e is a target for delta-reduction,
    and the given definition is the one to be expanded. */
optional<declaration> type_context::is_delta(expr const & e) const {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        if (auto d = m_env.find(const_name(f)))
            if (d->is_definition() && !is_opaque(*d))
                return d;
    }
    return none_declaration();
}

/** \brief Weak head normal form core procedure that performs delta reduction
    for non-opaque constants with definitional height greater than or equal to \c h.

    This method is based on <tt>whnf_core(expr const &)</tt> and \c unfold_names.
    \remark This method does not use normalization extensions attached in the environment.
*/
expr type_context::whnf_core(expr e, unsigned h) {
    while (true) {
        expr new_e = unfold_names(whnf_core(e), h);
        if (is_eqp(e, new_e))
            return e;
        e = new_e;
    }
}

/** \brief Put expression \c t in weak head normal form */
expr type_context::whnf(expr const & e) {
    // Do not cache easy cases
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local: case expr_kind::Pi:
        return e;
    case expr_kind::Lambda: case expr_kind::Macro: case expr_kind::App: case expr_kind::Constant:
        break;
    }

    expr t = e;
    while (true) {
        expr t1 = whnf_core(t, 0);
        if (auto new_t = norm_ext(t1)) {
            t  = *new_t;
        } else {
            return t1;
        }
    }
}

static bool is_max_like(level const & l) {
    return is_max(l) || is_imax(l);
}

lbool type_context::quick_is_def_eq(level const & l1, level const & l2) {
    if (is_equivalent(l1, l2)) {
        return l_true;
    }

    if (is_uvar(l1)) {
        if (auto v = get_assignment(l1)) {
            return quick_is_def_eq(*v, l2);
        } else {
            update_assignment(l1, l2);
            return l_true;
        }
    }

    if (is_uvar(l2)) {
        if (auto v = get_assignment(l2)) {
            return quick_is_def_eq(l1, *v);
        } else {
            update_assignment(l2, l1);
            return l_true;
        }
    }

    // postpone constraint if l1 or l2 is max, imax or meta.
    if (is_max_like(l1) || is_max_like(l2) || is_meta(l1) || is_meta(l2))
        return l_undef;

    if (l1.kind() == l2.kind()) {
        switch (l1.kind()) {
        case level_kind::Succ:
            return quick_is_def_eq(succ_of(l1), succ_of(l2));
        case level_kind::Param: case level_kind::Global:
            return l_false;
        case level_kind::Max:   case level_kind::IMax:
        case level_kind::Zero:  case level_kind::Meta:
            lean_unreachable();
        }
        lean_unreachable();
    } else {
        return l_false;
    }
}

bool type_context::full_is_def_eq(level const & l1, level const & l2) {
    if (is_equivalent(l1, l2)) {
        return true;
    }

    if (is_uvar(l1)) {
        if (auto v = get_assignment(l1)) {
            return full_is_def_eq(*v, l2);
        } else {
            update_assignment(l1, l2);
            return true;
        }
    }

    if (is_uvar(l2)) {
        if (auto v = get_assignment(l2)) {
            return full_is_def_eq(l1, *v);
        } else {
            update_assignment(l2, l1);
            return true;
        }
    }

    level new_l1 = normalize(instantiate_uvars(l1));
    level new_l2 = normalize(instantiate_uvars(l2));

    if (ignore_universe_def_eq(new_l1, new_l2))
        return true;

    if (l1 != new_l1 || l2 != new_l2)
        return full_is_def_eq(new_l1, new_l2);

    if (l1.kind() != l2.kind())
        return false;

    switch (l1.kind()) {
    case level_kind::Max:
        return
            full_is_def_eq(max_lhs(l1), max_lhs(l2)) &&
            full_is_def_eq(max_rhs(l1), max_rhs(l2));
    case level_kind::IMax:
        return
            full_is_def_eq(imax_lhs(l1), imax_lhs(l2)) &&
            full_is_def_eq(imax_rhs(l1), imax_rhs(l2));
    case level_kind::Succ:
        return full_is_def_eq(succ_of(l1), succ_of(l2));
    case level_kind::Param:
    case level_kind::Global:
        return false;
    case level_kind::Zero:
    case level_kind::Meta:
        lean_unreachable();
    }
    lean_unreachable();
}

bool type_context::is_def_eq(level const & l1, level const & l2) {
    auto r = quick_is_def_eq(l1, l2);
    if (r == l_undef) {
        m_postponed.emplace_back(l1, l2);
        return true;
    } else {
        return r == l_true;
    }
}

bool type_context::is_def_eq(levels const & ls1, levels const & ls2) {
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

/** \brief Given \c e of the form <tt>?m t_1 ... t_n</tt>, where
    ?m is an assigned mvar, substitute \c ?m with its assignment. */
expr type_context::subst_mvar(expr const & e) {
    buffer<expr> args;
    expr const & m   = get_app_rev_args(e, args);
    lean_assert(is_mvar(m));
    optional<expr> v = get_assignment(m);
    lean_assert(v);
    return apply_beta(*v, args.size(), args.data());
}

bool type_context::has_assigned_uvar(level const & l) const {
    if (!has_meta(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (!has_meta(l))
                return false; // stop search
            if (found)
                return false;  // stop search
            if (is_uvar(l) && is_assigned(l)) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

bool type_context::has_assigned_uvar(levels const & ls) const {
    for (level const & l : ls) {
        if (has_assigned_uvar(l))
            return true;
    }
    return false;
}

bool type_context::has_assigned_uvar_mvar(expr const & e) const {
    if (!has_expr_metavar(e) && !has_univ_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_univ_metavar(e))
                return false; // stop search
            if (found)
                return false; // stop search
            if ((is_mvar(e) && is_assigned(e)) ||
                (is_constant(e) && has_assigned_uvar(const_levels(e))) ||
                (is_sort(e) && has_assigned_uvar(sort_level(e)))) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

level type_context::instantiate_uvars(level const & l) {
    if (!has_assigned_uvar(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (is_uvar(l)) {
                if (auto v1 = get_assignment(l)) {
                    level v2 = instantiate_uvars(*v1);
                    if (*v1 != v2) {
                        update_assignment(l, v2);
                        return some_level(v2);
                    } else {
                        return some_level(*v1);
                    }
                }
            }
            return none_level();
        });
}

struct instantiate_uvars_mvars_fn : public replace_visitor {
    type_context & m_owner;

    level visit_level(level const & l) {
        return m_owner.instantiate_uvars(l);
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls,
                         [&](level const & l) { return visit_level(l); },
                         [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) {
        return update_constant(c, visit_levels(const_levels(c)));
    }

    virtual expr visit_local(expr const & e) {
        return update_mlocal(e, visit(mlocal_type(e)));
    }

    virtual expr visit_meta(expr const & m) {
        if (m_owner.is_mvar(m)) {
            if (auto v1 = m_owner.get_assignment(m)) {
                if (!has_expr_metavar(*v1)) {
                    return *v1;
                } else {
                    expr v2 = m_owner.instantiate_uvars_mvars(*v1);
                    if (v2 != *v1)
                        m_owner.update_assignment(m, v2);
                    return v2;
                }
            } else {
                return m;
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr const & f = get_app_rev_args(e, args);
        if (m_owner.is_mvar(f)) {
            if (auto v = m_owner.get_assignment(f)) {
                expr new_app = apply_beta(*v, args.size(), args.data());
                if (has_expr_metavar(new_app))
                    return visit(new_app);
                else
                    return new_app;
            }
        }
        expr new_f = visit(f);
        buffer<expr> new_args;
        bool modified = !is_eqp(new_f, f);
        for (expr const & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(arg, new_arg))
                modified = true;
            new_args.push_back(new_arg);
        }
        if (!modified)
            return e;
        else
            return mk_rev_app(new_f, new_args, e.get_tag());
    }

    virtual expr visit_macro(expr const & e) {
        lean_assert(is_macro(e));
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        return update_macro(e, new_args.size(), new_args.data());
    }

    virtual expr visit(expr const & e) {
        if (!has_expr_metavar(e) && !has_univ_metavar(e))
            return e;
        else
            return replace_visitor::visit(e);
    }

public:
    instantiate_uvars_mvars_fn(type_context & o):m_owner(o) {}

    expr operator()(expr const & e) { return visit(e); }
};

expr type_context::instantiate_uvars_mvars(expr const & e) {
    if (!has_assigned_uvar_mvar(e))
        return e;
    else
        return instantiate_uvars_mvars_fn(*this)(e);
}

bool type_context::is_prop(expr const & e) {
    if (m_env.impredicative()) {
        expr t   = whnf(infer(e));
        return t == mk_Prop();
    } else {
        return false;
    }
}

bool type_context::is_def_eq_binding(expr e1, expr e2) {
    lean_assert(e1.kind() == e2.kind());
    lean_assert(is_binding(e1));
    expr_kind k = e1.kind();
    buffer<expr> subst;
    do {
        optional<expr> var_e1_type;
        if (binding_domain(e1) != binding_domain(e2)) {
            var_e1_type = instantiate_rev(binding_domain(e1), subst.size(), subst.data());
            expr var_e2_type = instantiate_rev(binding_domain(e2), subst.size(), subst.data());
            if (!is_def_eq_core(var_e2_type, *var_e1_type))
                return false;
        }
        if (!closed(binding_body(e1)) || !closed(binding_body(e2))) {
            // local is used inside t or s
            if (!var_e1_type)
                var_e1_type = instantiate_rev(binding_domain(e1), subst.size(), subst.data());
            subst.push_back(mk_tmp_local(*var_e1_type));
        } else {
            expr const & dont_care = mk_Prop();
            subst.push_back(dont_care);
        }
        e1 = binding_body(e1);
        e2 = binding_body(e2);
    } while (e1.kind() == k && e2.kind() == k);
    return is_def_eq_core(instantiate_rev(e1, subst.size(), subst.data()),
                          instantiate_rev(e2, subst.size(), subst.data()));
}

bool type_context::is_def_eq_args(expr const & e1, expr const & e2) {
    lean_assert(is_app(e1) && is_app(e2));
    buffer<expr> args1, args2;
    get_app_args(e1, args1);
    get_app_args(e2, args2);
    if (args1.size() != args2.size())
        return false;
    for (unsigned i = 0; i < args1.size(); i++) {
        if (!is_def_eq_core(args1[i], args2[i]))
            return false;
    }
    return true;
}

bool type_context::is_def_eq_eta(expr const & e1, expr const & e2) {
    expr new_e1 = try_eta(e1);
    expr new_e2 = try_eta(e2);
    if (e1 != new_e1 || e2 != new_e2) {
        scope s(*this);
        if (is_def_eq_core(new_e1, new_e2)) {
            s.commit();
            return true;
        }
    }
    return false;
}

bool type_context::is_def_eq_proof_irrel(expr const & e1, expr const & e2) {
    if (!m_env.prop_proof_irrel())
        return false;
    expr e1_type = infer(e1);
    expr e2_type = infer(e2);
    if (is_prop(e1_type)) {
        scope s(*this);
        if (is_def_eq_core(e1_type, e2_type)) {
            s.commit();
            return true;
        }
    }
    return false;
}

/** \brief Given \c ma of the form <tt>?m t_1 ... t_n</tt>, (try to) assign
    ?m to (an abstraction of) v. Return true if success and false otherwise. */
bool type_context::process_assignment(expr const & ma, expr const & v) {
    buffer<expr> args;
    expr const & m = get_app_args(ma, args);
    buffer<expr> locals;
    for (expr & arg : args) {
        expr new_arg = arg;
        // try to instantiate
        if (is_meta(new_arg))
            new_arg = instantiate_uvars_mvars(arg);
        if (!is_local(new_arg))
            break; // it is not local
        arg = new_arg;
        lean_assert(is_local(arg));
        if (std::any_of(locals.begin(), locals.end(), [&](expr const & local) {
                    return mlocal_name(local) == mlocal_name(arg); }))
            break; // duplicate local
        locals.push_back(arg);
    }
    lean_assert(is_mvar(m));
    expr new_v = instantiate_uvars_mvars(v);

    if (!validate_assignment(m, locals, v))
        return false;

    if (m_check_types) {
        try {
            scope s(*this);
            expr t1 = infer(ma);
            expr t2 = infer(v);
            flet<bool> ignore_ext_mvar(m_ignore_external_mvars, true);
            if (!is_def_eq_core(t1, t2))
                return false;
            s.commit();
        } catch (exception &) {
            // We may fail to infer the type of ma or v because the type may contain meta-variables.
            // Example: ma may be of the form (?m a), and the type of ?m may be ?M where ?M is a
            // (external) metavariable created by the unifier.
            // We believe this only happens when we are interacting with the elaborator.
        }
    }

    if (args.empty()) {
        // easy case
        update_assignment(m, new_v);
        return true;
    } else if (args.size() == locals.size()) {
        update_assignment(m, Fun(locals, new_v));
        return true;
    } else {
        // This case is imprecise since it is not a higher order pattern.
        // That the term \c ma is of the form (?m t_1 ... t_n) and the t_i's are not pairwise
        // distinct local constants.
        expr m_type = infer_metavar(m);
        for (unsigned i = 0; i < args.size(); i++) {
            m_type = whnf(m_type);
            if (!is_pi(m_type))
                return false;
            lean_assert(i <= locals.size());
            if (i == locals.size())
                locals.push_back(mk_tmp_local(binding_domain(m_type)));
            lean_assert(i < locals.size());
            m_type = instantiate(binding_body(m_type), locals[i]);
        }
        lean_assert(locals.size() == args.size());
        update_assignment(m, Fun(locals, new_v));
        return true;
    }
}

bool type_context::assign(expr const & ma, expr const & v) {
    expr const & f = get_app_fn(ma);
    if (is_assigned(f)) {
        return is_def_eq(ma, v);
    } else {
        return process_assignment(ma, v);
    }
}

bool type_context::force_assign(expr const & ma, expr const & v) {
    return process_assignment(ma, v);
}

/** \brief This is an auxiliary method for is_def_eq. It handles the "easy cases". */
lbool type_context::quick_is_def_eq(expr const & e1, expr const & e2) {
    if (e1 == e2)
        return l_true;

    expr const & f1 = get_app_fn(e1);
    if (is_mvar(f1)) {
        if (is_assigned(f1)) {
            return to_lbool(is_def_eq_core(subst_mvar(e1), e2));
        } else {
            return to_lbool(process_assignment(e1, e2));
        }
    }

    expr const & f2 = get_app_fn(e2);
    if (is_mvar(f2)) {
        if (is_assigned(f2)) {
            return to_lbool(is_def_eq_core(e1, subst_mvar(e2)));
        } else {
            return to_lbool(process_assignment(e2, e1));
        }
    }

    if (m_ignore_external_mvars && (is_meta(e1) || is_meta(e2)))
        return l_true;

    if (e1.kind() == e2.kind()) {
        switch (e1.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return to_lbool(is_def_eq_binding(e1, e2));
        case expr_kind::Sort:
            return to_lbool(is_def_eq(sort_level(e1), sort_level(e2)));
        case expr_kind::Meta:  case expr_kind::Var:
        case expr_kind::Local: case expr_kind::App:
        case expr_kind::Constant: case expr_kind::Macro:
            // We do not handle these cases in this method.
            break;
        }
    }
    return l_undef; // This is not an "easy case"
}

auto type_context::lazy_delta_reduction_step(expr & t_n, expr & s_n) -> reduction_status {
    auto d_t = is_delta(t_n);
    auto d_s = is_delta(s_n);
    if (!d_t && !d_s) {
        return reduction_status::DefUnknown;
    } else if (d_t && !d_s) {
        t_n = whnf_core(unfold_names(t_n, 0));
    } else if (!d_t && d_s) {
        s_n = whnf_core(unfold_names(s_n, 0));
    } else if (d_t->get_height() > d_s->get_height()) {
        t_n = whnf_core(unfold_names(t_n, d_s->get_height() + 1));
    } else if (d_t->get_height() < d_s->get_height()) {
        s_n = whnf_core(unfold_names(s_n, d_t->get_height() + 1));
    } else {
        if (is_app(t_n) && is_app(s_n) && is_eqp(*d_t, *d_s)) {
            if (!is_opaque(*d_t)) {
                scope s(*this);
                if (is_def_eq_args(t_n, s_n) &&
                    is_def_eq(const_levels(get_app_fn(t_n)), const_levels(get_app_fn(s_n)))) {
                    s.commit();
                    return reduction_status::DefEqual;
                }
            }
        }
        t_n = whnf_core(unfold_names(t_n, d_t->get_height() - 1));
        s_n = whnf_core(unfold_names(s_n, d_s->get_height() - 1));
    }
    switch (quick_is_def_eq(t_n, s_n)) {
    case l_true:  return reduction_status::DefEqual;
    case l_false: return reduction_status::DefDiff;
    case l_undef: return reduction_status::Continue;
    }
    lean_unreachable();
}

lbool type_context::lazy_delta_reduction(expr & t_n, expr & s_n) {
    while (true) {
        switch (lazy_delta_reduction_step(t_n, s_n)) {
        case reduction_status::Continue:   break;
        case reduction_status::DefUnknown: return l_undef;
        case reduction_status::DefEqual:   return l_true;
        case reduction_status::DefDiff:    return l_false;
        }
    }
}

auto type_context::ext_reduction_step(expr & t_n, expr & s_n) -> reduction_status {
    auto new_t_n = norm_ext(t_n);
    auto new_s_n = norm_ext(s_n);
    if (!new_t_n && !new_s_n)
        return reduction_status::DefUnknown;
    if (new_t_n)
        t_n = whnf_core(*new_t_n);
    if (new_s_n)
        s_n = whnf_core(*new_s_n);
    switch (quick_is_def_eq(t_n, s_n)) {
    case l_true:  return reduction_status::DefEqual;
    case l_false: return reduction_status::DefDiff;
    case l_undef: return reduction_status::Continue;
    }
    lean_unreachable();
}

// Apply lazy delta-reduction and then normalizer extensions
lbool type_context::reduce_def_eq(expr & t_n, expr & s_n) {
    while (true) {
        // first, keep applying lazy delta-reduction while applicable
        lbool r = lazy_delta_reduction(t_n, s_n);
        if (r != l_undef) return r;

        // try normalizer extensions
        switch (ext_reduction_step(t_n, s_n)) {
        case reduction_status::Continue:   break;
        case reduction_status::DefUnknown: return l_undef;
        case reduction_status::DefEqual:   return l_true;
        case reduction_status::DefDiff:    return l_false;
        }
    }
}

bool type_context::is_def_eq_core(expr const & t, expr const & s) {
    check_system("is_definitionally_equal");
    lbool r = quick_is_def_eq(t, s);
    if (r != l_undef) return r == l_true;

    expr t_n = whnf_core(t);
    expr s_n = whnf_core(s);

    if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
        r = quick_is_def_eq(t_n, s_n);
        if (r != l_undef) return r == l_true;
    }

    r = reduce_def_eq(t_n, s_n);
    if (r != l_undef) return r == l_true;

    if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n)) {
        scope s(*this);
        if (is_def_eq(const_levels(t_n), const_levels(s_n))) {
            s.commit();
            return true;
        }
    }

    if (is_local(t_n) && is_local(s_n) && mlocal_name(t_n) == mlocal_name(s_n))
        return true;

    if (is_app(t_n) && is_app(s_n)) {
        scope s(*this);
        if (is_def_eq_args(t_n, s_n) &&
            is_def_eq_core(get_app_fn(t_n), get_app_fn(s_n))) {
            s.commit();
            return true;
        }
    }

    if (is_def_eq_eta(t_n, s_n))
        return true;

    if (is_def_eq_proof_irrel(t_n, s_n))
        return true;

    if (on_is_def_eq_failure(t_n, s_n))
        return is_def_eq_core(t_n, s_n);
    else
        return false;
}

bool type_context::process_postponed(unsigned old_sz) {
    if (m_postponed.size() == old_sz)
        return true; // no new universe constraints.
    lean_assert(m_postponed.size() > old_sz);
    buffer<pair<level, level>> b1, b2;
    b1.append(m_postponed.size() - old_sz, m_postponed.data() + old_sz);
    buffer<pair<level, level>> * curr, * next;
    curr = &b1;
    next = &b2;
    while (true) {
        for (auto p : *curr) {
            auto r = quick_is_def_eq(p.first, p.second);
            if (r == l_undef) {
                next->push_back(p);
            } else if (r == l_false) {
                return false;
            }
        }
        if (next->empty()) {
            return true; // all constraints have been processed
        } else if (next->size() < curr->size()) {
            // easy constraints have been processed in this iteration
            curr->clear();
            std::swap(next, curr);
            lean_assert(next->empty());
        } else {
            // use full (and approximate) is_def_eq to process the first constraint
            // in next.
            auto p = (*next)[0];
            if (!full_is_def_eq(p.first, p.second))
                return false;
            if (next->size() == 1)
                return true; // the last constraint has been solved.
            curr->clear();
            curr->append(next->size() - 1, next->data() + 1);
            next->clear();
        }
    }
}

bool type_context::is_def_eq(expr const & e1, expr const & e2) {
    scope s(*this);
    unsigned psz = m_postponed.size();
    if (!is_def_eq_core(e1, e2)) {
        return false;
    }
    if (process_postponed(psz)) {
        m_postponed.resize(psz);
        s.commit();
        return true;
    }
    return false;
}

expr type_context::infer_constant(expr const & e) {
    declaration d    = m_env.get(const_name(e));
    auto const & ps = d.get_univ_params();
    auto const & ls = const_levels(e);
    if (length(ps) != length(ls))
        throw exception("infer type failed, incorrect number of universe levels");
    return instantiate_type_univ_params(d, ls);
}

expr type_context::infer_macro(expr const & e) {
    auto def = macro_def(e);
    bool infer_only = true;
    // Remark: we are ignoring constraints generated by the macro definition.
    return def.check_type(e, *m_ext_ctx, infer_only).first;
}

expr type_context::infer_lambda(expr e) {
    buffer<expr> es, ds, ls;
    while (is_lambda(e)) {
        es.push_back(e);
        ds.push_back(binding_domain(e));
        expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr l = mk_tmp_local(d, binding_info(e));
        ls.push_back(l);
        e = binding_body(e);
    }
    expr t = infer(instantiate_rev(e, ls.size(), ls.data()));
    expr r = abstract_locals(t, ls.size(), ls.data());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = mk_pi(binding_name(es[i]), ds[i], r, binding_info(es[i]));
    }
    return r;
}

/** \brief Make sure \c e is a sort, if it is not throw an exception using \c ref as a reference */
void type_context::ensure_sort(expr const & e, expr const & /* ref */) {
    // Remark: for simplicity reasons, we just fail if \c e is not a sort.
    if (!is_sort(e))
        throw exception("infer type failed, sort expected");
}

expr type_context::infer_pi(expr const & e0) {
    buffer<expr>  ls;
    buffer<level> us;
    expr e = e0;
    while (is_pi(e)) {
        expr d      = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr d_type = whnf(infer(d));
        ensure_sort(d_type, e0);
        us.push_back(sort_level(d_type));
        expr l  = mk_tmp_local(d, binding_info(e));
        ls.push_back(l);
        e = binding_body(e);
    }
    e = instantiate_rev(e, ls.size(), ls.data());
    expr e_type = whnf(infer(e));
    ensure_sort(e_type, e0);
    level r = sort_level(e_type);
    unsigned i = ls.size();
    bool imp = m_env.impredicative();
    while (i > 0) {
        --i;
        r = imp ? mk_imax(us[i], r) : mk_max(us[i], r);
    }
    return mk_sort(r);
}

/** \brief Make sure \c e is a Pi-expression, if it is not throw an exception using \c ref as a reference */
void type_context::ensure_pi(expr const & e, expr const & /* ref */) {
    // Remark: for simplicity reasons, we just fail if \c e is not a Pi.
    if (!is_pi(e))
        throw exception("infer type failed, Pi expected");
    // Potential problem: e is of the form (f ...) where f is a constant that is not marked as reducible.
    // So, whnf does not reduce it, and we fail to detect that e is can be reduced to a Pi-expression.
}

expr type_context::infer_app(expr const & e) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    expr f_type = infer(f);
    unsigned j        = 0;
    unsigned nargs    = args.size();
    for (unsigned i = 0; i < nargs; i++) {
        if (is_pi(f_type)) {
            f_type = binding_body(f_type);
        } else {
            f_type = whnf(instantiate_rev(f_type, i-j, args.data()+j));
            ensure_pi(f_type, e);
            f_type = binding_body(f_type);
            j = i;
        }
    }
    return instantiate_rev(f_type, nargs-j, args.data()+j);
}

expr type_context::infer(expr const & e) {
    lean_assert(!is_var(e));
    lean_assert(closed(e));
    check_system("infer_type");

    expr r;
    switch (e.kind()) {
    case expr_kind::Local:
        r = infer_local(e);
        break;
    case expr_kind::Meta:
        r = infer_metavar(e);
        break;
    case expr_kind::Var:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Sort:
        r = mk_sort(mk_succ(sort_level(e)));
        break;
    case expr_kind::Constant:
        r = infer_constant(e);
        break;
    case expr_kind::Macro:
        r = infer_macro(e);
        break;
    case expr_kind::Lambda:
        r = infer_lambda(e);
        break;
    case expr_kind::Pi:
        r = infer_pi(e);
        break;
    case expr_kind::App:
        r = infer_app(e);
        break;
    }
    // TODO(Leo): cache results if we have performance problems
    return r;
}

void type_context::clear_cache() {
    m_ci_cache.clear();
}

/** \brief If the constant \c e is a class, return its name */
optional<name> type_context::constant_is_class(expr const & e) {
    name const & cls_name = const_name(e);
    if (lean::is_class(m_env, cls_name)) {
        return optional<name>(cls_name);
    } else {
        return optional<name>();
    }
}

optional<name> type_context::is_full_class(expr type) {
    type = whnf(type);
    if (is_pi(type)) {
        return is_full_class(instantiate(binding_body(type), mk_tmp_local(binding_domain(type))));
    } else {
        expr f = get_app_fn(type);
        if (!is_constant(f))
            return optional<name>();
        return constant_is_class(f);
    }
}

/** \brief Partial/Quick test for is_class. Result
    l_true:   \c type is a class, and the name of the class is stored in \c result.
    l_false:  \c type is not a class.
    l_undef:  procedure did not establish whether \c type is a class or not.
*/
lbool type_context::is_quick_class(expr const & type, name & result) {
    expr const * it         = &type;
    while (true) {
        switch (it->kind()) {
        case expr_kind::Var:  case expr_kind::Sort:   case expr_kind::Local:
        case expr_kind::Meta: case expr_kind::Lambda:
            return l_false;
        case expr_kind::Macro:
            return l_undef;
        case expr_kind::Constant:
            if (auto r = constant_is_class(*it)) {
                result = *r;
                return l_true;
            } else if (is_extra_opaque(const_name(*it))) {
                return l_false;
            } else {
                return l_undef;
            }
        case expr_kind::App: {
            expr const & f = get_app_fn(*it);
            if (is_constant(f)) {
                if (auto r = constant_is_class(f)) {
                    result = *r;
                    return l_true;
                } else if (is_extra_opaque(const_name(f))) {
                    return l_false;
                } else {
                    return l_undef;
                }
            } else if (is_lambda(f) || is_macro(f)) {
                return l_undef;
            } else {
                return l_false;
            }
        }
        case expr_kind::Pi:
            it = &binding_body(*it);
            break;
        }
    }
}

/** \brief Return true iff \c type is a class or Pi that produces a class. */
optional<name> type_context::is_class(expr const & type) {
    name result;
    switch (is_quick_class(type, result)) {
    case l_true:  return optional<name>(result);
    case l_false: return optional<name>();
    case l_undef: break;
    }
    return is_full_class(type);
}

bool type_context::compatible_local_instances(list<expr> const & ctx) {
    unsigned i = 0;
    for (expr const & e : ctx) {
        // Remark: we use infer_type(e) instead of mlocal_type because we want to allow
        // customers (e.g., blast) of this class to store the type of local constants
        // in a different place.
        if (auto cname = is_class(infer(e))) {
            if (i == m_ci_local_instances.size())
                return false; // ctx has more local instances than m_ci_local_instances
            if (e != m_ci_local_instances[i].second)
                return false; // local instance in ctx is not compatible with one at m_ci_local_instances
            i++;
        }
    }
    return i == m_ci_local_instances.size();
}

// Helper function for find_unsynth_metavar
static bool has_meta_arg(expr e) {
    while (is_app(e)) {
        if (is_meta(app_arg(e)))
            return true;
        e = app_fn(e);
    }
    return false;
}

/** IF \c e is of the form (f ... (?m t_1 ... t_n) ...) where ?m is an unassigned
    metavariable whose type is a type class, and (?m t_1 ... t_n) must be synthesized
    by type class resolution, then we return ?m.
    Otherwise, we return none */
optional<pair<expr, expr>> type_context::find_unsynth_metavar(expr const & e) {
    if (!has_meta_arg(e))
        return optional<pair<expr, expr>>();
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    expr type       = infer(fn);
    unsigned i      = 0;
    while (i < args.size()) {
        type = whnf(type);
        if (!is_pi(type))
            return optional<pair<expr, expr>>();
        expr const & arg = args[i];
        if (binding_info(type).is_inst_implicit() && is_meta(arg)) {
            expr const & m = get_app_fn(arg);
            if (is_mvar(m)) {
                expr m_type = instantiate_uvars_mvars(infer(m));
                if (!has_expr_metavar_relaxed(m_type)) {
                    return some(mk_pair(m, m_type));
                }
            }
        }
        type = instantiate(binding_body(type), arg);
        i++;
    }
    return optional<pair<expr, expr>>();
}

bool type_context::on_is_def_eq_failure(expr & e1, expr & e2) {
    if (is_app(e1) && is_app(e2)) {
        if (auto p1 = find_unsynth_metavar(e1)) {
            if (mk_nested_instance(p1->first, p1->second)) {
                e1 = instantiate_uvars_mvars(e1);
                return true;
            }
        }
        if (auto p2 = find_unsynth_metavar(e2)) {
            if (mk_nested_instance(p2->first, p2->second)) {
                e2 = instantiate_uvars_mvars(e2);
                return true;
            }
        }
    }
    return false;
}

bool type_context::validate_assignment(expr const & m, buffer<expr> const & locals, expr const & v) {
    // We must check
    //   1. Any (internal) local constant occurring in v occurs in locals
    //   2. m does not occur in v
    bool ok = true;
    for_each(v, [&](expr const & e, unsigned) {
            if (!ok)
                return false; // stop search
            if (is_tmp_local(e)) {
                if (std::all_of(locals.begin(), locals.end(), [&](expr const & a) {
                            return mlocal_name(a) != mlocal_name(e); })) {
                    ok = false; // failed 1
                    return false;
                }
            } else if (is_mvar(e)) {
                if (m == e) {
                    ok = false; // failed 2
                    return false;
                }
                return false;
            }
            return true;
        });
    return ok;
}

bool type_context::update_options(options const & opts) {
    options o = opts;
    unsigned max_depth    = get_class_instance_max_depth(o);
    bool trans_instances  = get_class_trans_instances(o);
    bool trace_instances  = get_class_trace_instances(o);
    if (trace_instances) {
        o = o.update_if_undef(get_pp_purify_metavars_name(), false);
        o = o.update_if_undef(get_pp_implicit_name(), true);
    }
    bool r = true;
    if (m_ci_max_depth        != max_depth        ||
        m_ci_trans_instances  != trans_instances  ||
        m_ci_trace_instances  != trace_instances) {
        r = false;
    }
    m_ci_max_depth        = max_depth;
    m_ci_trans_instances  = trans_instances;
    m_ci_trace_instances  = trace_instances;
    m_ios.set_options(o);
    return r;
}

[[ noreturn ]] static void throw_class_exception(char const * msg, expr const & m) { throw_generic_exception(msg, m); }
[[ noreturn ]] static void throw_class_exception(expr const & m, pp_fn const & fn) { throw_generic_exception(m, fn); }

io_state_stream type_context::diagnostic() {
    return lean::diagnostic(m_env, m_ios);
}

void type_context::trace(unsigned depth, expr const & mvar, expr const & mvar_type, expr const & r) {
    lean_assert(m_ci_trace_instances);
    auto out = diagnostic();
    if (!m_ci_displayed_trace_header && m_ci_choices.size() == m_ci_choices_ini_sz + 1) {
        if (m_pip) {
            if (auto fname = m_pip->get_file_name()) {
                out << fname << ":";
            }
            if (m_ci_pos)
                out << m_ci_pos->first << ":" << m_ci_pos->second << ":";
        }
        out << " class-instance resolution trace" << endl;
        m_ci_displayed_trace_header = true;
    }
    for (unsigned i = 0; i < depth; i++)
        out << " ";
    if (depth > 0)
        out << "[" << depth << "] ";
    out << mvar << " : " << instantiate_uvars_mvars(mvar_type) << " := " << r << endl;
}

// Try to synthesize e.m_mvar using instance inst : inst_type.
// trans_inst is true if inst is a transitive instance.
bool type_context::try_instance(ci_stack_entry const & e, expr const & inst, expr const & inst_type, bool trans_inst) {
    try {
        buffer<expr> locals;
        expr const & mvar = e.m_mvar;
        expr mvar_type = mlocal_type(mvar);
        while (true) {
            mvar_type = whnf(mvar_type);
            if (!is_pi(mvar_type))
                break;
            expr local  = mk_tmp_local(binding_domain(mvar_type));
            locals.push_back(local);
            mvar_type = instantiate(binding_body(mvar_type), local);
        }
        expr type  = inst_type;
        expr r     = inst;
        buffer<expr> new_inst_mvars;
        while (true) {
            type = whnf(type);
            if (!is_pi(type))
                break;
            expr new_mvar = mk_mvar(Pi(locals, binding_domain(type)));
            if (binding_info(type).is_inst_implicit()) {
                new_inst_mvars.push_back(new_mvar);
            }
            expr new_arg = mk_app(new_mvar, locals);
            r    = mk_app(r, new_arg);
            type = instantiate(binding_body(type), new_arg);
        }
        if (m_ci_trace_instances) {
            trace(e.m_depth, mk_app(mvar, locals), mvar_type, r);
        }
        if (!is_def_eq(mvar_type, type)) {
            return false;
        }
        r = Fun(locals, r);
        // Remark: if the metavariable is already assigned, we should check whether
        // the previous assignment (obtained by solving unification constraints) and the
        // synthesized one are definitionally equal. We don't do that for performance reasons.
        // Moreover, the is_def_eq defined here is not complete (e.g., it only unfolds reducible constants).
        update_assignment(mvar, r);
        // copy new_inst_mvars to stack
        unsigned i = new_inst_mvars.size();
        while (i > 0) {
            --i;
            m_ci_state.m_stack = cons(ci_stack_entry(new_inst_mvars[i], e.m_depth+1, trans_inst), m_ci_state.m_stack);
        }
        return true;
    } catch (exception &) {
        return false;
    }
}

bool type_context::try_instance(ci_stack_entry const & e, name const & inst_name, bool trans_inst) {
    if (auto decl = m_env.find(inst_name)) {
        buffer<level> ls_buffer;
        unsigned num_univ_ps = decl->get_num_univ_params();
        for (unsigned i = 0; i < num_univ_ps; i++)
            ls_buffer.push_back(mk_uvar());
        levels ls = to_list(ls_buffer.begin(), ls_buffer.end());
        expr inst_cnst = mk_constant(inst_name, ls);
        expr inst_type = instantiate_type_univ_params(*decl, ls);
        return try_instance(e, inst_cnst, inst_type, trans_inst);
    } else {
        return false;
    }
}

list<expr> type_context::get_local_instances(name const & cname) {
    buffer<expr> selected;
    for (pair<name, expr> const & p : m_ci_local_instances) {
        if (p.first == cname)
            selected.push_back(p.second);
    }
    return to_list(selected);
}

bool type_context::is_ci_done() const {
    return empty(m_ci_state.m_stack);
}

bool type_context::mk_choice_point(expr const & mvar) {
    lean_assert(is_mvar(mvar));
    if (m_ci_choices.size() > m_ci_choices_ini_sz + m_ci_max_depth) {
        throw_class_exception("maximum class-instance resolution depth has been reached "
                              "(the limit can be increased by setting option 'class.instance_max_depth') "
                              "(the class-instance resolution trace can be visualized "
                              "by setting option 'class.trace_instances')",
                              infer(m_ci_main_mvar));
    }
    // Remark: we initially tried to reject branches where mvar_type contained unassigned metavariables.
    // The idea was to make the procedure easier to understand.
    // However, it turns out this is too restrictive. The group_theory folder contains the following instance.
    //     nsubg_setoid : Π {A : Type} [s : group A] (N : set A) [is_nsubg : @is_normal_subgroup A s N], setoid A
    // When it is used, it creates a subproblem for
    //    is_nsubg : @is_normal_subgroup A s ?N
    // where ?N is not known. Actually, we can only find the value for ?N by constructing the instance is_nsubg.
    expr mvar_type = instantiate_uvars_mvars(mlocal_type(mvar));
    bool toplevel_choice = m_ci_choices.empty();
    m_ci_choices.push_back(ci_choice());
    push();
    ci_choice & r = m_ci_choices.back();
    auto cname = is_class(mvar_type);
    if (!cname)
        return false;
    r.m_local_instances = get_local_instances(*cname);
    if (m_ci_trans_instances && toplevel_choice) {
        // we only use transitive instances in the top-level
        r.m_trans_instances = get_class_derived_trans_instances(m_env, *cname);
    }
    r.m_instances = get_class_instances(m_env, *cname);
    if (empty(r.m_local_instances) && empty(r.m_trans_instances) && empty(r.m_instances))
        return false;
    r.m_state = m_ci_state;
    return true;
}

bool type_context::process_next_alt_core(ci_stack_entry const & e, list<expr> & insts) {
    while (!empty(insts)) {
        expr inst       = head(insts);
        insts           = tail(insts);
        expr inst_type  = infer(inst);
        bool trans_inst = false;
        if (try_instance(e, inst, inst_type, trans_inst))
            return true;
    }
    return false;
}

bool type_context::process_next_alt_core(ci_stack_entry const & e, list<name> & inst_names, bool trans_inst) {
    while (!empty(inst_names)) {
        name inst_name    = head(inst_names);
        inst_names        = tail(inst_names);
        if (try_instance(e, inst_name, trans_inst))
            return true;
    }
    return false;
}

bool type_context::process_next_alt(ci_stack_entry const & e) {
    lean_assert(m_ci_choices.size() > m_ci_choices_ini_sz);
    lean_assert(!m_ci_choices.empty());
    std::vector<ci_choice> & cs = m_ci_choices;
    list<expr> locals = cs.back().m_local_instances;
    if (process_next_alt_core(e, locals)) {
        cs.back().m_local_instances = locals;
        return true;
    }
    cs.back().m_local_instances = list<expr>();
    if (!e.m_trans_inst_subproblem) {
        list<name> trans_insts = cs.back().m_trans_instances;
        if (process_next_alt_core(e, trans_insts, true)) {
            cs.back().m_trans_instances = trans_insts;
            return true;
        }
        cs.back().m_trans_instances = list<name>();
        list<name> insts = cs.back().m_instances;
        if (process_next_alt_core(e, insts, false)) {
            cs.back().m_instances = insts;
            return true;
        }
        cs.back().m_instances = list<name>();
    }
    return false;
}

bool type_context::process_next_mvar() {
    lean_assert(!is_ci_done());
    ci_stack_entry e = head(m_ci_state.m_stack);
    if (!mk_choice_point(e.m_mvar))
        return false;
    m_ci_state.m_stack = tail(m_ci_state.m_stack);
    return process_next_alt(e);
}

bool type_context::backtrack() {
    if (m_ci_choices.size() == m_ci_choices_ini_sz)
        return false;
    lean_assert(!m_ci_choices.empty());
    while (true) {
        m_ci_choices.pop_back();
        pop();
        if (m_ci_choices.size() == m_ci_choices_ini_sz)
            return false;
        m_ci_state         = m_ci_choices.back().m_state;
        ci_stack_entry e   = head(m_ci_state.m_stack);
        m_ci_state.m_stack = tail(m_ci_state.m_stack);
        if (process_next_alt(e))
            return true;
    }
}

optional<expr> type_context::search() {
    while (!is_ci_done()) {
        if (!process_next_mvar()) {
            if (!backtrack())
                return none_expr();
        }
    }
    return some_expr(instantiate_uvars_mvars(m_ci_main_mvar));
}

optional<expr> type_context::next_solution() {
    if (m_ci_choices.size() == m_ci_choices_ini_sz)
        return none_expr();
    pop(); push(); // restore assignment
    m_ci_state         = m_ci_choices.back().m_state;
    ci_stack_entry e   = head(m_ci_state.m_stack);
    m_ci_state.m_stack = tail(m_ci_state.m_stack);
    if (process_next_alt(e))
        return search();
    else if (backtrack())
        return search();
    else
        return none_expr();
}

void type_context::init_search(expr const & type) {
    m_ci_state          = ci_state();
    m_ci_main_mvar      = mk_mvar(type);
    m_ci_state.m_stack  = to_list(ci_stack_entry(m_ci_main_mvar, 0));
    m_ci_choices_ini_sz = m_ci_choices.size();
}

optional<expr> type_context::check_ci_cache(expr const & type) const {
    if (m_ci_multiple_instances) {
        // We do not cache results when multiple instances have to be generated.
        return none_expr();
    }
    auto it = m_ci_cache.find(type);
    if (it != m_ci_cache.end())
        return some_expr(it->second);
    else
        return none_expr();
}

void type_context::cache_ci_result(expr const & type, expr const & inst) {
    if (m_ci_multiple_instances) {
        // We do not cache results when multiple instances have to be generated.
        return;
    }
    m_ci_cache.insert(mk_pair(type, inst));
}

optional<expr> type_context::ensure_no_meta(optional<expr> r) {
    while (true) {
        if (!r)
            return none_expr();
        if (!has_expr_metavar_relaxed(*r)) {
            cache_ci_result(mlocal_type(m_ci_main_mvar), *r);
            return r;
        }
        r = next_solution();
    }
}

optional<expr> type_context::mk_class_instance_core(expr const & type) {
    if (auto r = check_ci_cache(type)) {
        if (m_ci_trace_instances) {
            diagnostic() << "cached instance for " << type << "\n" << *r << "\n";
        }
        return r;
    }
    init_search(type);
    auto r = search();
    return ensure_no_meta(r);
}

void type_context::restore_choices(unsigned old_sz) {
    lean_assert(old_sz <= m_ci_choices.size());
    while (m_ci_choices.size() > old_sz) {
        m_ci_choices.pop_back();
        pop();
    }
    lean_assert(m_ci_choices.size() == old_sz);
}

optional<expr> type_context::mk_class_instance(expr const & type) {
    m_ci_choices.clear();
    ci_choices_scope scope(*this);
    m_ci_displayed_trace_header = false;
    auto r = mk_class_instance_core(type);
    if (r)
        scope.commit();
    return r;
}

optional<expr> type_context::next_class_instance() {
    if (!m_ci_multiple_instances)
        return none_expr();
    auto r = next_solution();
    return ensure_no_meta(r);
}

/** \brief Create a nested type class instance of the given type
    \remark This method is used to resolve nested type class resolution problems. */
optional<expr> type_context::mk_nested_instance(expr const & type) {
    ci_choices_scope scope(*this);
    flet<unsigned> save_choice_sz(m_ci_choices_ini_sz, m_ci_choices_ini_sz);
    flet<ci_state> save_state(m_ci_state, ci_state());
    flet<expr>     save_main_mvar(m_ci_main_mvar, expr());
    unsigned old_choices_sz = m_ci_choices.size();
    auto r = mk_class_instance_core(type);
    if (r)
        scope.commit();
    m_ci_choices.resize(old_choices_sz); // cut search
    return r;
}

/** \brief Create a nested type class instance of the given type, and assign it to metavariable \c m.
    Return true iff the instance was successfully created.
    \remark This method is used to resolve nested type class resolution problems. */
bool type_context::mk_nested_instance(expr const & m, expr const & m_type) {
    lean_assert(is_mvar(m));
    if (auto r = mk_nested_instance(m_type)) {
        update_assignment(m, *r);
        return true;
    } else {
        return false;
    }
}

type_context::scope_pos_info::scope_pos_info(type_context & o, pos_info_provider const * pip, expr const & pos_ref):
    m_owner(o),
    m_old_pip(m_owner.m_pip),
    m_old_pos(m_owner.m_ci_pos) {
    m_owner.m_pip = pip;
    if (pip)
        m_owner.m_ci_pos = pip->get_pos_info(pos_ref);
}

type_context::scope_pos_info::~scope_pos_info() {
    m_owner.m_pip    = m_old_pip;
    m_owner.m_ci_pos = m_old_pos;
}

default_type_context::default_type_context(environment const & env, io_state const & ios,
                                               list<expr> const & ctx, bool multiple_instances):
    type_context(env, ios, multiple_instances),
    m_not_reducible_pred(mk_not_reducible_pred(env)) {
    m_ignore_if_zero = false;
    m_next_local_idx = 0;
    m_next_uvar_idx  = 0;
    m_next_mvar_idx  = 0;
    set_context(ctx);
}

default_type_context::~default_type_context() {}

expr default_type_context::mk_tmp_local(expr const & type, binder_info const & bi) {
    unsigned idx = m_next_local_idx;
    m_next_local_idx++;
    name n(*g_prefix, idx);
    return lean::mk_local(n, n, type, bi);
}

bool default_type_context::is_tmp_local(expr const & e) const {
    if (!is_local(e))
        return false;
    name const & n = mlocal_name(e);
    return !n.is_atomic() && n.get_prefix() == *g_prefix;
}

bool default_type_context::is_uvar(level const & l) const {
    if (!is_meta(l))
        return false;
    name const & n = meta_id(l);
    return !n.is_atomic() && n.get_prefix() == *g_prefix;
}

bool default_type_context::is_mvar(expr const & e) const {
    if (!is_metavar(e))
        return false;
    name const & n = mlocal_name(e);
    return !n.is_atomic() && n.get_prefix() == *g_prefix;
}

unsigned default_type_context::uvar_idx(level const & l) const {
    lean_assert(is_uvar(l));
    return meta_id(l).get_numeral();
}

unsigned default_type_context::mvar_idx(expr const & m) const {
    lean_assert(is_mvar(m));
    return mlocal_name(m).get_numeral();
}

optional<level> default_type_context::get_assignment(level const & u) const {
    if (auto v = m_assignment.m_uassignment.find(uvar_idx(u)))
        return some_level(*v);
    else
        return none_level();
}

optional<expr> default_type_context::get_assignment(expr const & m) const {
    if (auto v = m_assignment.m_eassignment.find(mvar_idx(m)))
        return some_expr(*v);
    else
        return none_expr();
}

void default_type_context::update_assignment(level const & u, level const & v) {
    m_assignment.m_uassignment.insert(uvar_idx(u), v);
}

void default_type_context::update_assignment(expr const & m, expr const & v) {
    m_assignment.m_eassignment.insert(mvar_idx(m), v);
}

level default_type_context::mk_uvar() {
    unsigned idx = m_next_uvar_idx;
    m_next_uvar_idx++;
    return mk_meta_univ(name(*g_prefix, idx));
}

expr default_type_context::mk_mvar(expr const & type) {
    unsigned idx = m_next_mvar_idx;
    m_next_mvar_idx++;
    return mk_metavar(name(*g_prefix, idx), type);
}

bool default_type_context::ignore_universe_def_eq(level const & l1, level const & l2) const {
    if (is_meta(l1) || is_meta(l2)) {
        // The unifier may invoke this module before universe metavariables in the class
        // have been instantiated. So, we just ignore and assume they will be solved by
        // the unifier.

        // See comment at m_ignore_if_zero declaration.
        if (m_ignore_if_zero && (is_zero(l1) || is_zero(l2)))
            return false;
        return true; // we ignore
    } else {
        return false;
    }
}

void initialize_type_context() {
    g_prefix = new name(name::mk_internal_unique_name());
    g_class_trace_instances        = new name{"class", "trace_instances"};
    g_class_instance_max_depth     = new name{"class", "instance_max_depth"};
    g_class_trans_instances        = new name{"class", "trans_instances"};
    register_bool_option(*g_class_trace_instances,  LEAN_DEFAULT_CLASS_TRACE_INSTANCES,
                         "(class) display messages showing the class-instances resolution execution trace");

    register_unsigned_option(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH,
                             "(class) max allowed depth in class-instance resolution");

    register_bool_option(*g_class_trans_instances,  LEAN_DEFAULT_CLASS_TRANS_INSTANCES,
                         "(class) use automatically derived instances from the transitive closure of "
                         "the structure instance graph");
}

void finalize_type_context() {
    delete g_prefix;
    delete g_class_trace_instances;
    delete g_class_instance_max_depth;
    delete g_class_trans_instances;
}
}
