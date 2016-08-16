/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/app_builder.h"
#include "library/replace_visitor_with_tc.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/structural_rec.h"

namespace lean {
#define trace_struct(Code) lean_trace(name({"eqn_compiler", "structural_rec"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); Code)

struct structural_rec_fn {
    type_context & m_ctx;
    structural_rec_fn(type_context & ctx):m_ctx(ctx) {}

    /** \brief Auxiliary object for checking whether recursive application are
        structurally smaller or not */
    struct check_rhs_fn {
        type_context & m_ctx;
        expr           m_lhs;
        expr           m_fn;
        expr           m_pattern;
        unsigned       m_arg_idx;

        check_rhs_fn(type_context & ctx, expr const & lhs, expr const & fn, expr const & pattern, unsigned arg_idx):
            m_ctx(ctx), m_lhs(lhs), m_fn(fn), m_pattern(pattern), m_arg_idx(arg_idx) {}

        bool is_constructor(expr const & e) const {
            return static_cast<bool>(eqns_env_interface(m_ctx).is_constructor(e));
        }

        /** \brief Return true iff \c s is structurally smaller than \c t OR equal to \c t */
        bool is_le(expr const & s, expr const & t) {
            return m_ctx.is_def_eq(s, t) || is_lt(s, t);
        }

        /** Return true iff \c s is structurally smaller than \c t */
        bool is_lt(expr s, expr t) {
            s = m_ctx.whnf(s);
            t = m_ctx.whnf(t);
            if (is_app(s)) {
                expr const & s_fn = get_app_fn(s);
                if (!is_constructor(s_fn))
                    return is_lt(s_fn, t); // f < t ==> s := f a_1 ... a_n < t
            }
            buffer<expr> t_args;
            expr const & t_fn = get_app_args(t, t_args);
            if (!is_constructor(t_fn))
                return false;
            return std::any_of(t_args.begin(), t_args.end(),
                               [&](expr const & t_arg) { return is_le(s, t_arg); });
        }

        /** \brief Return true iff all recursive applications in \c e are structurally smaller than \c m_pattern. */
        bool check_rhs(expr const & e) {
            switch (e.kind()) {
            case expr_kind::Var:   case expr_kind::Meta:
            case expr_kind::Local: case expr_kind::Constant:
            case expr_kind::Sort:
                return true;
            case expr_kind::Macro:
                for (unsigned i = 0; i < macro_num_args(e); i++)
                    if (!check_rhs(macro_arg(e, i)))
                        return false;
                return true;
            case expr_kind::App: {
                buffer<expr> args;
                expr const & fn = get_app_args(e, args);
                if (!check_rhs(fn))
                    return false;
                for (unsigned i = 0; i < args.size(); i++)
                    if (!check_rhs(args[i]))
                        return false;
                if (is_local(fn) && mlocal_name(fn) == mlocal_name(m_fn)) {
                    /* recusive application */
                    if (m_arg_idx < args.size()) {
                        expr const & arg = args[m_arg_idx];
                        /* arg must be structurally smaller than m_pattern */
                        if (!is_lt(arg, m_pattern)) {
                            trace_struct(tout() << "structural recursion on argument #" << (m_arg_idx+1) << " was not used "
                                         << "for '" << m_fn << "'\nargument #" << (m_arg_idx+1)
                                         << " in the application\n  "
                                         << e << "\nis not structurally smaller than the one occurring in "
                                         << "the equation left-hand-side\n  "
                                         << m_lhs << "\n";);
                            return false;
                        }
                    } else {
                        /* function is not fully applied */
                        trace_struct(tout() << "structural recursion on argument #" << (m_arg_idx+1) << " was not used "
                                     << "for '" << m_fn << "' because of the partial application\n  "
                                     << e << "\n";);
                        return false;
                    }
                }
                return true;
            }
            case expr_kind::Let:
                if (!check_rhs(let_value(e))) {
                    return false;
                } else {
                    type_context::tmp_locals locals(m_ctx);
                    return check_rhs(instantiate(let_body(e), locals.push_local_from_let(e)));
                }
            case expr_kind::Lambda:
            case expr_kind::Pi:
                if (!check_rhs(binding_domain(e))) {
                    return false;
                } else {
                    type_context::tmp_locals locals(m_ctx);
                    return check_rhs(instantiate(binding_body(e), locals.push_local_from_binding(e)));
                }
            }
            lean_unreachable();
        }

        bool operator()(expr const & e) {
            return check_rhs(e);
        }
    };

    bool check_rhs(expr const & lhs, expr const & fn, expr pattern, unsigned arg_idx, expr const & rhs) {
        pattern = m_ctx.whnf(pattern);
        return check_rhs_fn(m_ctx, lhs, fn, pattern, arg_idx)(rhs);
    }

    bool check_eq(expr const & eqn, unsigned arg_idx) {
        unpack_eqn ue(m_ctx, eqn);
        buffer<expr> args;
        expr const & fn  = get_app_args(ue.lhs(), args);
        return check_rhs(ue.lhs(), fn, args[arg_idx], arg_idx, ue.rhs());
    }

    static bool depends_on_locals(expr const & e, type_context::tmp_locals const & locals) {
        return depends_on_any(e, locals.as_buffer().size(), locals.as_buffer().data());
    }

    bool check_arg_type(unpack_eqns const & ues, unsigned arg_idx) {
        type_context::tmp_locals locals(m_ctx);
        /* We can only use structural recursion on arg_idx IF
           1- Type is an inductive datatype with support for the brec_on construction.
           2- Type parameters do not depend on other arguments of the function being defined. */
        expr fn      = ues.get_fn(0);
        expr fn_type = m_ctx.infer(fn);
        for (unsigned i = 0; i < arg_idx; i++) {
            fn_type = m_ctx.whnf(fn_type);
            if (!is_pi(fn_type)) throw_ill_formed_eqns();
            fn_type = instantiate(binding_body(fn_type), locals.push_local_from_binding(fn_type));
        }
        if (!is_pi(fn_type)) throw_ill_formed_eqns();
        expr arg_type = binding_domain(fn_type);
        buffer<expr> I_args;
        expr I        = get_app_args(arg_type, I_args);
        if (!eqns_env_interface(m_ctx).is_inductive(I)) {
            trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                         << "for '" << fn << "' because type is not inductive\n  "
                         << arg_type << "\n";);
            return false;
        }
        if (!m_ctx.env().find(name(const_name(I), "brec_on"))) {
            trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                         << "for '" << fn << "' because the inductive type '" << I << "' does have brec_on recursor\n  "
                         << arg_type << "\n";);
            return false;
        }
        unsigned nindices = eqns_env_interface(m_ctx).get_inductive_num_indices(const_name(I));
        if (nindices > 0) {
            trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                         << "for '" << fn << "' because the inductive type '" << I << "' is an indexed family\n  "
                         << arg_type << "\n";);
            return false;
        }
        if (depends_on_locals(arg_type, locals)) {
            trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                         << "for '" << fn << "' because type parameter depends on previous arguments\n  "
                         << arg_type << "\n";);
            return false;
        }
        return true;
    }

    optional<unsigned> find_rec_arg(unpack_eqns const & ues) {
        buffer<expr> const & eqns = ues.get_eqns_of(0);
        unsigned arity = ues.get_arity_of(0);
        for (unsigned i = 0; i < arity; i++) {
            if (check_arg_type(ues, i)) {
                bool ok = true;
                for (expr const & eqn : eqns) {
                    if (!check_eq(eqn, i)) {
                        ok = false;
                        break;
                    }
                }
                if (ok) return optional<unsigned>(i);
            }
        }
        return optional<unsigned>();
    }

    /* Return the type of the new function, and the type of the motive for below/brec_on */
    pair<expr, expr> mk_new_fn_motive_types(unpack_eqns const & ues, unsigned arg_idx) {
        type_context::tmp_locals locals(m_ctx);
        expr fn        = ues.get_fn(0);
        expr fn_type   = m_ctx.infer(fn);
        unsigned arity = ues.get_arity_of(0);
        expr rec_arg;
        buffer<expr> other_args;
        for (unsigned i = 0; i < arity; i++) {
            fn_type = m_ctx.whnf(fn_type);
            if (!is_pi(fn_type)) throw_ill_formed_eqns();
            expr arg = locals.push_local_from_binding(fn_type);
            if (i == arg_idx) {
                rec_arg = arg;
            } else {
                other_args.push_back(arg);
            }
            fn_type  = instantiate(binding_body(fn_type), arg);
        }
        buffer<expr> I_args;
        expr I = get_app_args(m_ctx.infer(rec_arg), I_args);
        expr  motive = m_ctx.mk_pi(other_args, fn_type);
        level u      = get_level(m_ctx, motive);
        motive       = m_ctx.mk_lambda(rec_arg, motive);
        lean_assert(is_constant(I));
        buffer<level> below_lvls;
        below_lvls.push_back(u);
        for (level const & v : const_levels(I))
            below_lvls.push_back(v);
        expr below       = mk_app(mk_constant(name(const_name(I), "below"), to_list(below_lvls)), I_args);
        expr motive_type = binding_domain(m_ctx.relaxed_whnf(m_ctx.infer(below)));
        below            = mk_app(below, motive, rec_arg);
        locals.push_local("_F", below);
        return mk_pair(locals.mk_pi(fn_type), motive_type);
    }

    struct elim_rec_apps_failed {};

    struct elim_rec_apps_fn : public replace_visitor_with_tc {
        expr           m_fn;
        unsigned       m_arg_idx;
        expr           m_F;
        expr           m_C;

        elim_rec_apps_fn(type_context & ctx, expr const & fn,
                         unsigned arg_idx, expr const & F, expr const & C):
            replace_visitor_with_tc(ctx),
            m_fn(fn), m_arg_idx(arg_idx), m_F(F), m_C(C) {}

        /** \brief Retrieve result for \c a from the below dictionary \c d. \c d is a term made of products,
            and m_C (the abstract local). */
        optional<expr> to_below(expr const & d, expr const & a, expr const & F) {
            expr const & fn = get_app_fn(d);
            if (is_constant(fn, get_prod_name())) {
                expr d_arg1 = m_ctx.whnf(app_arg(app_fn(d)));
                expr d_arg2 = m_ctx.whnf(app_arg(d));
                if (auto r = to_below(d_arg1, a, mk_pr1(m_ctx, F)))
                    return r;
                else if (auto r = to_below(d_arg2, a, mk_pr2(m_ctx, F)))
                    return r;
                else
                    return none_expr();
            } else if (is_local(fn)) {
                if (mlocal_name(m_C) == mlocal_name(fn) && m_ctx.is_def_eq(app_arg(d), a))
                    return some_expr(F);
                return none_expr();
            } else if (is_pi(d)) {
                if (is_app(a)) {
                    expr new_d = m_ctx.whnf(instantiate(binding_body(d), app_arg(a)));
                    return to_below(new_d, a, mk_app(F, app_arg(a)));
                } else {
                    return none_expr();
                }
            } else {
                return none_expr();
            }
        }

        expr elim(buffer<expr> const & args, tag g) {
            /* Replace motives with abstract one m_C.
               We use the abstract motive m_C as "marker". */
            buffer<expr> below_args;
            expr const & below_cnst = get_app_args(m_ctx.infer(m_F), below_args);
            below_args[below_args.size() - 2] = m_C;
            expr abst_below   = mk_app(below_cnst, below_args);
            expr below_dict   = m_ctx.whnf(abst_below);
            expr rec_arg      = m_ctx.whnf(args[m_arg_idx]);
            if (optional<expr> b = to_below(below_dict, rec_arg, m_F)) {
                expr r = *b;
                for (unsigned i = 0; i < args.size(); i++) {
                    if (i != m_arg_idx)
                        r = mk_app(r, args[i], g);
                }
                return r;
            } else {
                throw elim_rec_apps_failed();
            }
        }

        virtual expr visit_local(expr const & e) {
            if (mlocal_name(e) == mlocal_name(m_fn)) {
                /* unexpected occurrence of recursive function */
                throw elim_rec_apps_failed();
            }
            return e;
        }

        virtual expr visit_app(expr const & e) {
            expr const & fn = get_app_fn(e);
            if (is_local(fn) && mlocal_name(fn) == mlocal_name(m_fn)) {
                buffer<expr> args;
                get_app_args(e, args);
                if (m_arg_idx >= args.size()) throw elim_rec_apps_failed();
                buffer<expr> new_args;
                for (expr const & arg : args)
                    new_args.push_back(visit(arg));
                return elim(new_args, e.get_tag());
            } else {
                return replace_visitor_with_tc::visit_app(e);
            }
        }
    };

    void update_eqs(unpack_eqns & ues, expr const & fn, expr const & new_fn, unsigned arg_idx, expr const & motive_type) {
        /* C is a temporary "abstract" motive, we use it to access the "brec_on dictionary".
           The "brec_on dictionary is an element of type below, and it is the last argument of the new function. */
        expr C = mk_local(mk_fresh_name(), "_C", motive_type, binder_info());
        buffer<expr> & eqns = ues.get_eqns_of(0);
        for (expr & eqn : eqns) {
            unpack_eqn ue(m_ctx, eqn);
            expr lhs = ue.lhs();
            expr rhs = ue.rhs();
            buffer<expr> lhs_args;
            get_app_args(lhs, lhs_args);
            expr new_lhs = mk_app(new_fn, lhs_args);
            expr type    = m_ctx.whnf(m_ctx.infer(new_lhs));
            lean_assert(is_pi(type));
            expr F       = ue.add_var(binding_name(type), binding_domain(type));
            new_lhs      = mk_app(new_lhs, F);
            ue.lhs()     = new_lhs;
            ue.rhs()     = elim_rec_apps_fn(m_ctx, fn, arg_idx, F, C)(rhs);
            eqn          = ue.repack();
        }
    }

    optional<expr> operator()(expr const & e, unsigned & arg_idx) {
        unpack_eqns ues(m_ctx, e);
        if (ues.get_num_fns() != 1) {
            trace_struct(tout() << "structural recursion is not supported for mutually recursive functions:";
                         for (unsigned i = 0; i < ues.get_num_fns(); i++)
                             tout() << " " << ues.get_fn(i);
                         tout() << "\n";);
            return none_expr();
        }
        optional<unsigned> r = find_rec_arg(ues);
        if (!r) return none_expr();
        arg_idx = *r;
        expr fn = ues.get_fn(0);
        trace_struct(tout() << "using structural recursion on argument #" << (arg_idx+1) <<
                     " for '" << fn << "'\n";);
        expr new_fn_type, motive_type;
        std::tie(new_fn_type, motive_type) = mk_new_fn_motive_types(ues, arg_idx);
        trace_struct(
            tout() << "\n";
            tout() << "new function type: " << new_fn_type << "\n";
            tout() << "motive type:       " << motive_type << "\n";);
        expr new_fn = ues.update_fn_type(0, new_fn_type);
        try {
            update_eqs(ues, fn, new_fn, arg_idx, motive_type);
        } catch (elim_rec_apps_failed &) {
            trace_struct(tout() << "failed to compile equations/match using structural recursion, "
                         << "when creating new set of equations\n";);
            return none_expr();
        }
        expr new_eqns = ues.repack();
        trace_struct(tout() << "result:\n" << new_eqns << "\n";);
        return some_expr(new_eqns);
    }
};

optional<expr> try_structural_rec(type_context & ctx, expr const & e, unsigned & arg_idx) {
    return structural_rec_fn(ctx)(e, arg_idx);
}

void initialize_structural_rec() {
    register_trace_class({"eqn_compiler", "structural_rec"});
}
void finalize_structural_rec() {}
}
