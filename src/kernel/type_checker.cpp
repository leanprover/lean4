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
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/max_sharing.h"
#include "kernel/free_vars.h"
#include "kernel/metavar.h"
#include "kernel/error_msgs.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"

namespace lean {
static name g_x_name("x");

no_constraints_allowed_exception::no_constraints_allowed_exception():exception("constraints are not allowed in this type checker") {}
exception * no_constraints_allowed_exception::clone() const { return new no_constraints_allowed_exception(); }
void no_constraints_allowed_exception::rethrow() const { throw *this; }

void no_constraint_handler::add_cnstr(constraint const &) {
    throw no_constraints_allowed_exception();
}

/** \brief Auxiliary functional object used to implement type checker. */
struct type_checker::imp {
    /** \brief Interface type_checker <-> converter */
    class converter_context : public converter::context {
        imp & m_imp;
    public:
        converter_context(imp & i):m_imp(i) {}
        virtual name mk_fresh_name() { return m_imp.m_gen.next(); }
        virtual expr infer_type(expr const & e) { return m_imp.infer_type(e); }
        virtual void add_cnstr(constraint const & c) { m_imp.add_cnstr(c); }
    };

    /** \brief Interface type_checker <-> macro & normalizer_extension */
    class type_checker_context : public extension_context {
        imp & m_imp;
    public:
        type_checker_context(imp & i):m_imp(i) {}
        virtual environment const & env() const { return m_imp.m_env; }
        virtual expr whnf(expr const & e) { return m_imp.whnf(e); }
        virtual expr infer_type(expr const & e) { return m_imp.infer_type(e); }
        virtual name mk_fresh_name() { return m_imp.m_gen.next(); }
        virtual void add_cnstr(constraint const & c) { m_imp.add_cnstr(c); }
    };

    environment                m_env;
    name_generator             m_gen;
    constraint_handler &       m_chandler;
    std::unique_ptr<converter> m_conv;
    expr_struct_map<expr>      m_infer_type_cache;
    converter_context          m_conv_ctx;
    type_checker_context       m_tc_ctx;
    bool                       m_memoize;
    // temp flag
    param_names                m_params;

    imp(environment const & env, name_generator const & g, constraint_handler & h, std::unique_ptr<converter> && conv, bool memoize):
        m_env(env), m_gen(g), m_chandler(h), m_conv(std::move(conv)), m_conv_ctx(*this), m_tc_ctx(*this),
        m_memoize(memoize) {}

    optional<expr> expand_macro(expr const & m) {
        lean_assert(is_macro(m));
        if (auto new_m = macro_def(m).expand(macro_num_args(m), macro_args(m), m_tc_ctx))
            return some_expr(max_sharing(*new_m));
        else
            return none_expr();
    }

    /**
        \brief Return the body of the given binder, where the free variable #0 is replaced with a fresh local constant.
        It also returns the fresh local constant.
     */
    std::pair<expr, expr> open_binder_body(expr const & e) {
        expr local     = mk_local(m_gen.next() + binder_name(e), binder_domain(e));
        return mk_pair(instantiate(binder_body(e), local), local);
    }

    /** \brief Add given constraint to the constraint handler m_chandler. */
    void add_cnstr(constraint const & c) {
        m_chandler.add_cnstr(c);
    }

    /** \brief Return true iff \c t and \c s are definitionally equal */
    bool is_def_eq(expr const & t, expr const & s, delayed_justification & jst) {
        return m_conv->is_def_eq(t, s, m_conv_ctx, jst);
    }

    /** \brief Return true iff \c e is a proposition */
    bool is_prop(expr const & e) {
        return whnf(infer_type(e)) == Bool;
    }

    /**
       \brief Given a metavariable application ((?m t_1) ... t_k)
       Create a telescope with the types of t_1 ... t_k.
       If t_i is a local constant, then we abstract the occurrences of t_i in the types of t_{i+1} ... t_k.
       Return false if the telescope still contains local constants after the abstraction step.
    */
    bool meta_to_telescope(expr const & e, buffer<expr> & telescope) {
        lean_assert(is_meta(e));
        lean_assert(closed(e));
        buffer<optional<expr>> locals;
        return meta_to_telescope_core(e, telescope, locals);
    }

    /**
       \brief Auxiliary method for meta_to_telescope
    */
    bool meta_to_telescope_core(expr const & e, buffer<expr> & telescope, buffer<optional<expr>> & locals) {
        lean_assert(is_meta(e));
        if (is_app(e)) {
            if (!meta_to_telescope_core(app_fn(e), telescope, locals))
                return false;
            // infer type and abstract local constants
            unsigned n = locals.size();
            expr t = replace(infer_type(app_arg(e)),
                             [&](expr const & e, unsigned offset) -> optional<expr> {
                                 if (is_local(e)) {
                                     for (unsigned i = 0; i < n; i++) {
                                         if (locals[i] && is_eqp(*locals[i], e))
                                             return some_expr(mk_var(offset + n - i - 1));
                                     }
                                 }
                                 return none_expr();
                             });
            if (has_local(t))
                return false;
            telescope.push_back(t);
            if (is_local(e))
                locals.push_back(some_expr(e));
            else
                locals.push_back(none_expr());
        }
        return true;
    }

    /**
       \brief Make sure \c e "is" a sort, and return the corresponding sort.
       If \c e is not a sort, then the whnf procedure is invoked. Then, there are
       two options: the normalize \c e is a sort, or it is a meta. If it is a meta,
       a new constraint is created forcing it to be a sort.

       \remark \c s is used to extract position (line number information) when an
       error message is produced
    */
    expr ensure_sort(expr e, expr const & s) {
        if (is_sort(e))
            return e;
        e = whnf(e);
        if (is_sort(e)) {
            return e;
        } else if (is_meta(e)) {
            expr r = mk_sort(mk_meta_univ(m_gen.next()));
            justification j = mk_justification(s,
                                               [=](formatter const & fmt, options const & o, substitution const & subst) {
                                                   return pp_type_expected(fmt, m_env, o, subst.instantiate_metavars_wo_jst(s));
                                               });
            add_cnstr(mk_eq_cnstr(e, r, j));
            return r;
        } else {
            throw_kernel_exception(m_env, s,
                                   [=](formatter const & fmt, options const & o) { return pp_type_expected(fmt, m_env, o, s); });
        }
    }

    expr mk_tele_pi(buffer<expr> const & telescope, expr const & range) {
        expr r = range;
        unsigned i = telescope.size();
        while (i > 0) {
            --i;
            r = mk_pi(name(g_x_name, i), telescope[i], r);
        }
        return r;
    }

    /** \brief Similar to \c ensure_sort, but makes sure \c e "is" a Pi. */
    expr ensure_pi(expr e, expr const & s) {
        if (is_pi(e))
            return e;
        e = whnf(e);
        if (is_pi(e)) {
            return e;
        } else if (is_meta(e)) {
            buffer<expr> telescope;
            if (!meta_to_telescope(e, telescope))
                throw_kernel_exception(m_env, s,
                                       [=](formatter const & fmt, options const & o) { return pp_function_expected(fmt, m_env, o, s); });
            expr ta    = mk_sort(mk_meta_univ(m_gen.next()));
            expr A     = mk_metavar(m_gen.next(), mk_tele_pi(telescope, ta));
            expr A_xs  = mk_app_vars(A, telescope.size());
            telescope.push_back(A_xs);
            expr tb    = mk_sort(mk_meta_univ(m_gen.next()));
            expr B     = mk_metavar(m_gen.next(), mk_tele_pi(telescope, tb));
            buffer<expr> args;
            get_app_args(e, args);
            expr A_args = mk_app(A, args.size(), args.data());
            args.push_back(Var(0));
            expr B_args = mk_app(B, args.size(), args.data());
            expr r      = mk_pi(g_x_name, A, B);
            justification j = mk_justification(s,
                                               [=](formatter const & fmt, options const & o, substitution const & subst) {
                                                   return pp_function_expected(fmt, m_env, o, subst.instantiate_metavars_wo_jst(s));
                                               });
            add_cnstr(mk_eq_cnstr(e, r, j));
            return r;
        } else {
            throw_kernel_exception(m_env, s,
                                   [=](formatter const & fmt, options const & o) { return pp_function_expected(fmt, m_env, o, s); });
        }
    }

    /** \brief Create a justification for the level constraint <tt>lhs <= rhs</tt> associated with constanc \c c. */
    justification mk_lvl_cnstr_jst(expr const & c, level const & lhs, level const & rhs) {
        lean_assert(is_constant(c));
        return mk_justification(c,
                                [=](formatter const & fmt, options const & o, substitution const & subst) {
                                    return pp_def_lvl_cnstrs_satisfied(fmt, m_env, o,
                                                                       subst.instantiate_metavars_wo_jst(c),
                                                                       subst.instantiate_metavars_wo_jst(lhs),
                                                                       subst.instantiate_metavars_wo_jst(rhs));
                                });
    }

    /**
        \brief Create a justification for a application type mismatch,
        \c e is the application, \c fn_type and \c arg_type are the function and argument type.
    */
    justification mk_app_mismatch_jst(expr const & e, expr const & fn_type, expr const & arg_type) {
        lean_assert(is_app(e));
        return mk_justification(e,
                                [=](formatter const & fmt, options const & o, substitution const & subst) {
                                    return pp_app_type_mismatch(fmt, m_env, o,
                                                                subst.instantiate_metavars_wo_jst(e),
                                                                subst.instantiate_metavars_wo_jst(binder_domain(fn_type)),
                                                                subst.instantiate_metavars_wo_jst(arg_type));
                                });
    }

    /**
        \brief Create a justification for a let definition type mismatch,
        \c e is the let expression, and \c val_type is the type inferred for the let value.
    */
    justification mk_let_mismatch_jst(expr const & e, expr const & val_type) {
        lean_assert(is_let(e));
        return mk_justification(e,
                                [=](formatter const & fmt, options const & o, substitution const & subst) {
                                    return pp_def_type_mismatch(fmt, m_env, o, let_name(e),
                                                                subst.instantiate_metavars_wo_jst(let_type(e)),
                                                                subst.instantiate_metavars_wo_jst(val_type));
                                });
    }

    static constexpr char const * g_macro_error_msg = "failed to type check macro expansion";

    justification mk_macro_jst(expr const & e) {
        return mk_justification(e,
                                [=](formatter const &, options const &, substitution const &) {
                                    return format(g_macro_error_msg);
                                });
    }

    void check_level(level const & l) {
        if (auto n1 = get_undef_global(l, m_env))
            throw_kernel_exception(m_env, sstream() << "invalid reference to undefined global universe level '" << *n1 << "'");
        if (auto n2 = get_undef_param(l, m_params))
            throw_kernel_exception(m_env, sstream() << "invalid reference to undefined universe level parameter '" << *n2 << "'");
    }

    /**
        \brief Return type of expression \c e, if \c infer_only is false, then it also check whether \c e is type correct or not.

        \pre closed(e)
    */
    expr infer_type_core(expr const & e, bool infer_only) {
        lean_assert(closed(e));
        check_system("type checker");

        if (m_memoize) {
            auto it = m_infer_type_cache.find(e);
            if (it != m_infer_type_cache.end())
                return it->second;
        }

        expr r;
        switch (e.kind()) {
        case expr_kind::Local: case expr_kind::Meta:
            r = mlocal_type(e);
            break;
        case expr_kind::Var:
            throw_kernel_exception(m_env, "type checker does not support free variables, replace them with local constants before invoking it");
        case expr_kind::Sort:
            if (!infer_only)
                check_level(sort_level(e));
            r = mk_sort(mk_succ(sort_level(e)));
            break;
        case expr_kind::Constant: {
            definition d    = m_env.get(const_name(e));
            auto const & ps = d.get_params();
            auto const & ls = const_level_params(e);
            if (length(ps) != length(ls))
                throw_kernel_exception(m_env, sstream() << "incorrect number of universe levels parameters for '" << const_name(e) << "', #"
                                       << length(ps)  << " expected, #" << length(ls) << " provided");
            if (!infer_only) {
                for (level const & l : ls)
                    check_level(l);
            }
            r = instantiate_params(d.get_type(), ps, ls);
            break;
        }
        case expr_kind::Macro: {
            buffer<expr> arg_types;
            for (unsigned i = 0; i < macro_num_args(e); i++)
                arg_types.push_back(infer_type_core(macro_arg(e, i), infer_only));
            r = macro_def(e).get_type(macro_num_args(e), macro_args(e), arg_types.data(), m_tc_ctx);
            if (!infer_only && macro_def(e).trust_level() <= m_env.trust_lvl()) {
                optional<expr> m = expand_macro(e);
                if (!m)
                    throw_kernel_exception(m_env, "failed to expand macro", some_expr(e));
                expr t = infer_type_core(*m, infer_only);
                delayed_justification jst([=]() { return mk_macro_jst(e); });
                if (!is_def_eq(r, t, jst))
                    throw_kernel_exception(m_env, g_macro_error_msg, some_expr(e));
            }
            break;
        }
        case expr_kind::Lambda: {
            if (!infer_only) {
                expr t = infer_type_core(binder_domain(e), infer_only);
                ensure_sort(t, binder_domain(e));
            }
            auto b = open_binder_body(e);
            r = mk_pi(binder_name(e), binder_domain(e), abstract_p(infer_type_core(b.first, infer_only), b.second), binder_info(e));
            break;
        }
        case expr_kind::Pi: {
            expr t1 = ensure_sort(infer_type_core(binder_domain(e), infer_only), binder_domain(e));
            auto b  = open_binder_body(e);
            expr t2 = ensure_sort(infer_type_core(b.first, infer_only), binder_body(e));
            if (m_env.impredicative())
                r = mk_sort(mk_imax(sort_level(t1), sort_level(t2)));
            else
                r = mk_sort(mk_max(sort_level(t1), sort_level(t2)));
            break;
        }
        case expr_kind::App: {
            expr f_type = ensure_pi(infer_type_core(app_fn(e), infer_only), app_fn(e));
            if (!infer_only) {
                expr a_type = infer_type_core(app_arg(e), infer_only);
                delayed_justification jst([=]() { return mk_app_mismatch_jst(e, f_type, a_type); });
                if (!is_def_eq(a_type, binder_domain(f_type), jst)) {
                    throw_kernel_exception(m_env, e,
                                           [=](formatter const & fmt, options const & o) {
                                               return pp_app_type_mismatch(fmt, m_env, o, e, binder_domain(f_type), a_type);
                                           });
                }
            }
            r = instantiate(binder_body(f_type), app_arg(e));
            break;
        }
        case expr_kind::Let:
            if (!infer_only) {
                ensure_sort(infer_type_core(let_type(e), infer_only), let_type(e));
                expr val_type  = infer_type_core(let_value(e), infer_only);
                delayed_justification jst([=]() { return mk_let_mismatch_jst(e, val_type); });
                if (!is_def_eq(val_type, let_type(e), jst)) {
                    throw_kernel_exception(m_env, e,
                                           [=](formatter const & fmt, options const & o) {
                                               return pp_def_type_mismatch(fmt, m_env, o, let_name(e), let_type(e), val_type);
                                           });
                }
            }
            r = infer_type_core(instantiate(let_body(e), let_value(e)), infer_only);
            break;
        }

        if (m_memoize)
            m_infer_type_cache.insert(mk_pair(e, r));

        return r;
    }

    expr infer_type(expr const & e) { return infer_type_core(e, true); }
    expr check(expr const & e, param_names const & ps) {
        flet<param_names> updt(m_params, ps);
        return infer_type_core(e, false);
    }
    bool is_def_eq(expr const & t, expr const & s) { return m_conv->is_def_eq(t, s, m_conv_ctx); }
    expr whnf(expr const & t) { return m_conv->whnf(t, m_conv_ctx); }
};

no_constraint_handler g_no_constraint_handler;

type_checker::type_checker(environment const & env, name_generator const & g, constraint_handler & h, std::unique_ptr<converter> && conv, bool memoize):
    m_ptr(new imp(env, g, h, std::move(conv), memoize)) {}

type_checker::type_checker(environment const & env, name_generator const & g, std::unique_ptr<converter> && conv, bool memoize):
    type_checker(env, g, g_no_constraint_handler, std::move(conv), memoize) {}

static name g_tmp_prefix = name::mk_internal_unique_name();

type_checker::type_checker(environment const & env):
    type_checker(env, name_generator(g_tmp_prefix), g_no_constraint_handler, mk_default_converter(env), true) {}

type_checker::~type_checker() {}
expr type_checker::infer(expr const & t) { return m_ptr->infer_type(t); }
expr type_checker::check(expr const & t, param_names const & ps) { return m_ptr->check(t, ps); }
bool type_checker::is_def_eq(expr const & t, expr const & s) { return m_ptr->is_def_eq(t, s); }
bool type_checker::is_prop(expr const & t) { return m_ptr->is_prop(t); }
expr type_checker::whnf(expr const & t) { return m_ptr->whnf(t); }
expr type_checker::ensure_pi(expr const & t) { return m_ptr->ensure_pi(t, t); }
expr type_checker::ensure_sort(expr const & t) { return m_ptr->ensure_sort(t, t); }

static void check_no_metavar(environment const & env, expr const & e) {
    if (has_metavar(e))
        throw kernel_exception(env, "failed to add declaration to environment, it contains metavariables");
}

static void check_no_local(environment const & env, expr const & e) {
    if (has_local(e))
        throw kernel_exception(env, "failed to add declaration to environment, it contains local constants");
}

static void check_no_mlocal(environment const & env, expr const & e) {
    check_no_metavar(env, e);
    check_no_local(env, e);
}

static void check_name(environment const & env, name const & n) {
    if (env.find(n))
        throw_already_declared(env, n);
}

certified_definition check(environment const & env, definition const & d, name_generator const & g, name_set const & extra_opaque, bool memoize) {
    check_no_mlocal(env, d.get_type());
    if (d.is_definition())
        check_no_mlocal(env, d.get_value());
    check_name(env, d.get_name());

    type_checker checker1(env, g, mk_default_converter(env, optional<module_idx>(), memoize, extra_opaque));
    checker1.check(d.get_type(), d.get_params());
    if (d.is_definition()) {
        optional<module_idx> midx;
        if (d.is_opaque())
            midx = optional<module_idx>(d.get_module_idx());
        type_checker checker2(env, g, mk_default_converter(env, midx, memoize, extra_opaque));
        expr val_type = checker2.check(d.get_value(), d.get_params());
        if (!checker2.is_def_eq(val_type, d.get_type())) {
            throw_kernel_exception(env, d.get_value(),
                                   [=](formatter const & fmt, options const & o) {
                                       return pp_def_type_mismatch(fmt, env, o, d.get_name(), d.get_type(), val_type);
                                   });
        }
    }
    return certified_definition(env.get_id(), d);
}

certified_definition check(environment const & env, definition const & d, name_set const & extra_opaque, bool memoize) {
    return check(env, d, name_generator(g_tmp_prefix), extra_opaque, memoize);
}
}
