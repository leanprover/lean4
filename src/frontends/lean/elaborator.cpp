/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/list_fn.h"
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/error_msgs.h"
#include "kernel/expr_maps.h"
#include "library/coercion.h"
#include "library/placeholder.h"
#include "library/choice.h"
#include "library/explicit.h"
#include "library/unifier.h"
#include "frontends/lean/parameter.h"

namespace lean {
class elaborator {
    typedef scoped_map<expr, expr, expr_hash_alloc, expr_eqp> cache;
    typedef list<parameter> context;
    typedef std::vector<constraint> constraints;

    environment    m_env;
    io_state       m_ios;
    unifier_plugin m_plugin;
    name_generator m_ngen;
    type_checker   m_tc;
    substitution   m_subst;
    context        m_ctx;
    cache          m_cache;
    justification  m_accumulated; // accumulate justification of eagerly used substitutions
    constraints    m_constraints;

    /**
        \brief Auxiliary object for creating backtracking points.

        \remark A scope can only be created when m_constraints and m_subst are empty,
        and m_accumulated is none.
    */
    struct scope {
        elaborator & m_main;
        context      m_old_ctx;
        scope(elaborator & e, context const & ctx, substitution const & s):m_main(e) {
            lean_assert(m_main.m_constraints.empty());
            lean_assert(m_main.m_accumulated.is_none());
            m_old_ctx    = m_main.m_ctx;
            m_main.m_ctx = ctx;
            m_main.m_tc.push();
            m_main.m_cache.push();
            m_main.m_subst = s;
        }
        ~scope() {
            m_main.m_ctx = m_old_ctx;
            m_main.m_tc.pop();
            m_main.m_cache.pop();
            m_main.m_constraints.clear();
            m_main.m_accumulated = justification();
            m_main.m_subst = substitution();
            lean_assert(m_main.m_constraints.empty());
            lean_assert(m_main.m_accumulated.is_none());
        }
    };

    struct choice_elaborator {
        elaborator & m_elab;
        expr         m_choice;
        context      m_ctx;
        substitution m_subst;
        unsigned     m_idx;
        choice_elaborator(elaborator & elab, expr const & c, context const & ctx, substitution const & s):
            m_elab(elab), m_choice(c), m_ctx(ctx), m_subst(s), m_idx(0) {
        }

        optional<a_choice> next() {
            while (m_idx < get_num_choices(m_choice)) {
                expr const & c = get_choice(m_choice, m_idx);
                m_idx++;
                try {
                    scope s(m_elab, m_ctx, m_subst);
                    expr r = m_elab.visit(c);
                    justification j = m_elab.m_accumulated;
                    list<constraint> cs = to_list(m_elab.m_constraints.begin(), m_elab.m_constraints.end());
                    return optional<a_choice>(r, j, cs);
                } catch (exception &) {}
            }
            return optional<a_choice>();
        }
    };

    lazy_list<a_choice> choose(std::shared_ptr<choice_elaborator> const & c) {
        return mk_lazy_list<a_choice>([=]() {
                auto s = c->next();
                if (s)
                    return some(mk_pair(*s, choose(c)));
                else
                    return lazy_list<a_choice>::maybe_pair();
            });
    }

public:
    elaborator(environment const & env, io_state const & ios, name_generator const & ngen,
               substitution const & s = substitution(), context const & ctx = context()):
        m_env(env), m_ios(ios),
        m_plugin([](constraint const &, name_generator const &) { return lazy_list<list<constraint>>(); }),
        m_ngen(ngen), m_tc(env, m_ngen.mk_child(), [=](constraint const & c) { add_cnstr(c); },
                           mk_default_converter(m_env, optional<module_idx>(0))),
        m_subst(s), m_ctx(ctx) {
    }

    expr mk_local(name const & n, expr const & t) { return ::lean::mk_local(m_ngen.next(), n, t); }
    expr infer_type(expr const & e) {
        lean_assert(closed(e));
        return m_tc.infer(e); }
    expr whnf(expr const & e) { return m_tc.whnf(e); }

    /** \brief Clear constraint buffer \c m_constraints, and associated datastructures
        \c m_subst and \c m_accumulated.

        \remark \c m_subst contains solutions obtained by eagerly solving the "easy" constraints
        in \c m_subst, and \c m_accumulated store the justifications of all substitutions eagerly
        applied.
    */
    void clear_constraints() {
        m_constraints.clear();
        m_subst = substitution();
        m_accumulated = justification();
    }

    void add_cnstr_core(constraint const & c) {
        m_constraints.push_back(c);
    }

    /**
        \brief Add \c c to \c m_constraints, but also tries to update \c m_subst using \c c.
        The idea is to "populate" \c m_subst using easy/simple constraints.
        This trick improves the number of places where coercions can be applied.
        In the future, we may also use this information to implement eager pruning of choice
        constraints.

        \remark The justification \c m_accumulated is "appended" to \c c.
        This justification justifies all substitutions used.

        \remark By appeding \c m_accumulated we know we are not missing any dependency,
        but this is a coarse approximation of that actual dependencies.
    */
    void add_cnstr(constraint c) {
        if (!m_accumulated.is_none())
            c = update_justification(c, mk_composite1(c.get_justification(), m_accumulated));
        add_cnstr_core(c);
        auto ss = unify_simple(m_subst, c);
        m_subst = ss.second;
        if (ss.first == unify_status::Failed)
            throw unifier_exception(c.get_justification());
    }

    /**
        \brief Eagerly instantiate metavars using \c m_subst.

        \remark We update \c m_accumulated with any justifications used.
    */
    expr instantiate_metavars(expr const & e) {
        auto e_j = m_subst.instantiate_metavars(e);
        m_accumulated = mk_composite1(m_accumulated, e_j.second);
        return e_j.first;
    }

    static expr save_tag(expr && e, tag g) {
        e.set_tag(g);
        return e;
    }

    /**
       \brief Given <tt>e[l_1, ..., l_n]</tt> and assuming \c m_ctx is
            <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
       then the result is
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), e[x_1, ... x_n])</tt>.
    */
    expr pi_abstract_context(expr e, tag g) {
        for (auto const & p : m_ctx)
            e = save_tag(Pi(p.m_local, e, p.m_bi), g);
        return e;
    }

    expr mk_app(expr const & f, expr const & a, tag g) {
        return save_tag(::lean::mk_app(f, a), g);
    }

    /**
       \brief Assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return <tt>(f l_1 ... l_n)</tt>.
    */
    expr apply_context(expr const & f, tag g) {
        buffer<expr> args;
        for (auto const & p : m_ctx)
            args.push_back(p.m_local);
        expr r = f;
        unsigned i = args.size();
        while (i > 0) {
            --i;
            r = mk_app(r, args[i], g);
        }
        return r;
    }

    /**
       \brief Assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
       return a fresh metavariable \c ?m with type
           <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
       where \c ?u is a fresh universe metavariable.
    */
    expr mk_type_metavar(tag g) {
        name n = m_ngen.next();
        expr s = save_tag(mk_sort(mk_meta_univ(m_ngen.next())), g);
        expr t = pi_abstract_context(s, g);
        return save_tag(::lean::mk_metavar(n, t), g);
    }

    /**
       \brief Assuming \c m_ctx is
            <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
       return <tt>(?m l_1 ... l_n)</tt> where \c ?m is a fresh metavariable with type
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
       and \c ?u is a fresh universe metavariable.

       \remark The type of the resulting expression is <tt>Type.{?u}</tt>
    */
    expr mk_type_meta(tag g) {
        return apply_context(mk_type_metavar(g), g);
    }

    /**
       \brief Given <tt>type[l_1, ..., l_n]</tt> and assuming \c m_ctx is
            <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
       then the result is a fresh metavariable \c ?m with type
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), type[x_1, ... x_n])</tt>.
       If <tt>type</tt> is none, then the result is a fresh metavariable \c ?m1 with type
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), ?m2 x1 .... xn)</tt>,
       where ?m2 is another fresh metavariable with type
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
       and \c ?u is a fresh universe metavariable.
    */
    expr mk_metavar(optional<expr> const & type, tag g) {
        name n      = m_ngen.next();
        expr r_type = type ? *type : mk_type_meta(g);
        expr t      = pi_abstract_context(r_type, g);
        return save_tag(::lean::mk_metavar(n, t), g);
    }

    /**
       \brief Given <tt>type[l_1, ..., l_n]</tt> and assuming \c m_ctx is
            <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
       return (?m l_1 ... l_n), where ?m is a fresh metavariable
       created using \c mk_metavar.

       \see mk_metavar
    */
    expr mk_meta(optional<expr> const & type, tag g) {
        return apply_context(mk_metavar(type, g), g);
    }

    expr visit_expecting_type(expr const & e) {
        if (is_placeholder(e) && !placeholder_type(e))
            return mk_type_meta(e.get_tag());
        else
            return visit(e);
    }

    expr visit_expecting_type_of(expr const & e, expr const & t) {
        if (is_placeholder(e) && !placeholder_type(e))
            return mk_meta(some_expr(t), e.get_tag());
        else if (is_choice(e))
            return visit_choice(e, some_expr(t));
        else
            return visit(e);
    }

    expr visit_choice(expr const & e, optional<expr> const & t) {
        lean_assert(is_choice(e));
        // Possible optimization: try to lookahead and discard some of the alternatives.
        expr m      = mk_meta(t, e.get_tag());
        context ctx = m_ctx;
        auto choice_fn = [=](expr const & /* t */, substitution const & s, name_generator const & /* ngen */) {
            return choose(std::make_shared<choice_elaborator>(*this, e, ctx, s));
        };
        justification j = mk_justification("overloading", some_expr(e));
        add_cnstr(mk_choice_cnstr(m, choice_fn, false, j));
        return m;
    }

    /**
        \brief Make sure \c f is really a function, if it is not, try to apply coercions.
        The result is a pair <tt>new_f, f_type</tt>, where new_f is the new value for \c f,
        and \c f_type is its type (and a Pi-expression)
    */
    std::pair<expr, expr> ensure_fun(expr f) {
        expr f_type = infer_type(f);
        if (!is_pi(f_type))
            f_type = whnf(f_type);
        if (!is_pi(f_type) && has_metavar(f_type)) {
            f_type = whnf(instantiate_metavars(f_type));
            if (!is_pi(f_type) && is_meta(f_type)) {
                // let type checker add constraint
                f_type = m_tc.ensure_pi(f_type, f);
            }
        }
        if (!is_pi(f_type)) {
            // try coercion to function-class
            optional<expr> c = get_coercion_to_fun(m_env, f_type);
            if (c) {
                f = mk_app(*c, f, f.get_tag());
                f_type = infer_type(f);
                lean_assert(is_pi(f_type));
            } else {
                environment env = m_env;
                throw_kernel_exception(env, f,
                                       [=](formatter const & fmt, options const & o) { return pp_function_expected(fmt, env, o, f); });
            }
        }
        lean_assert(is_pi(f_type));
        return mk_pair(f, f_type);
    }

    optional<expr> get_coercion(expr a_type, expr d_type, bool /* is_cast */) {
        // TODO(Leo): handle casts, subtypes, ...
        a_type = whnf(a_type);
        d_type = whnf(d_type);
        expr const & d_cls = get_app_fn(d_type);
        if (is_constant(d_cls))
            return ::lean::get_coercion(m_env, a_type, const_name(d_cls));
        else
            return none_expr();
    }

    expr visit_app(expr const & e) {
        expr f      = visit(app_fn(e));
        auto f_t    = ensure_fun(f);
        f           = f_t.first;
        expr d_type = binding_domain(f_t.second);
        expr a      = visit_expecting_type_of(app_arg(e), d_type);
        expr a_type = instantiate_metavars(infer_type(a));
        app_delayed_justification j(m_env, e, f_t.second, a_type);
        if (!m_tc.is_def_eq(a_type, d_type, j)) {
            // try coercions
            optional<expr> c     = get_coercion(a_type, d_type, binding_info(f_t.second).is_cast());
            bool coercion_worked = false;
            if (c) {
                expr new_a      = mk_app(*c, a, a.get_tag());
                expr new_a_type = instantiate_metavars(infer_type(new_a));
                coercion_worked = m_tc.is_def_eq(new_a_type, d_type, j);
            } else {
                coercion_worked = false;
            }
            if (!coercion_worked) {
                if (has_metavar(a_type) || has_metavar(d_type)) {
                    // rely on unification hints to solve this constraint
                    add_cnstr(mk_eq_cnstr(a_type, d_type, j.get()));
                } else {
                    environment env = m_env;
                    throw_kernel_exception(m_env, a,
                                           [=](formatter const & fmt, options const & o) {
                                               return pp_app_type_mismatch(fmt, env, o, e, d_type, a_type);
                                           });
                }
            }
        }
        return mk_app(f, a, e.get_tag());
    }

    expr visit_placeholder(expr const & e) {
        return mk_meta(placeholder_type(e), e.get_tag());
    }

    level replace_univ_placeholder(level const & l) {
        return replace(l, [&](level const & l) {
                if (is_placeholder(l))
                    return some_level(mk_meta_univ(m_ngen.next()));
                else
                    return none_level();
            });
    }

    expr visit_sort(expr const & e) {
        return update_sort(e, replace_univ_placeholder(sort_level(e)));
    }

    expr visit_macro(expr const & e) {
        // Remark: Macros are not meant to be used in the front end.
        // Perhaps, we should throw error.
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(visit(macro_arg(e, i)));
        return update_macro(e, args.size(), args.data());
    }

    expr visit_constant(expr const & e) {
        declaration d = m_env.get(const_name(e));
        buffer<level> ls;
        for (level const & l : const_levels(e))
            ls.push_back(replace_univ_placeholder(l));
        unsigned num_univ_params = length(d.get_univ_params());
        if (num_univ_params < ls.size())
            throw_kernel_exception(m_env, sstream() << "incorrect number of universe levels parameters for '" << const_name(e) << "', #"
                                   << num_univ_params << " expected, #" << ls.size() << " provided");
        // "fill" with meta universe parameters
        for (unsigned i = ls.size(); i < num_univ_params; i++)
            ls.push_back(mk_meta_univ(m_ngen.next()));
        lean_assert(num_univ_params == ls.size());
        return update_constant(e, to_list(ls.begin(), ls.end()));
    }

    /** \brief Make sure \c e is a type. If it is not, then try to apply coercions. */
    expr ensure_type(expr const & e) {
        expr t = infer_type(e);
        if (is_sort(t))
            return e;
        t = whnf(t);
        if (is_sort(t))
            return e;
        if (has_metavar(t)) {
            t = whnf(instantiate_metavars(t));
            if (is_sort(t))
                return e;
            if (is_meta(t)) {
                // let type checker add constraint
                m_tc.ensure_sort(t, e);
                return e;
            }
        }
        optional<expr> c = get_coercion_to_sort(m_env, t);
        if (c)
            return mk_app(*c, e, e.get_tag());
        environment env = m_env;
        throw_kernel_exception(env, e,
                               [=](formatter const & fmt, options const & o) { return pp_type_expected(fmt, env, o, e); });
    }

    expr visit_pi(expr const & e) {
        expr d   = ensure_type(visit_expecting_type(binding_domain(e)));
        expr l   = mk_local(binding_name(e), d);
        expr b   = instantiate(binding_body(e), l);
        if (binding_info(e).is_contextual()) {
            flet<context> set(m_ctx, cons(parameter(l, binding_info(e)), m_ctx));
            b = ensure_type(visit_expecting_type(b));
        } else {
            b = ensure_type(visit_expecting_type(b));
        }
        b = abstract(b, l);
        return update_binding(e, d, b);
    }

    expr visit_lambda(expr const & e) {
        expr d   = ensure_type(visit_expecting_type(binding_domain(e)));
        expr l   = mk_local(binding_name(e), d);
        expr b   = instantiate(binding_body(e), l);
        if (binding_info(e).is_contextual()) {
            flet<context> set(m_ctx, cons(parameter(l, binding_info(e)), m_ctx));
            b = visit(b);
        } else {
            b = visit(b);
        }
        b = abstract(b, l);
        return update_binding(e, d, b);
    }

    expr visit_core(expr const & e) {
        if (is_placeholder(e)) {
            return visit_placeholder(e);
        } else if (is_choice(e)) {
            return visit_choice(e, none_expr());
        } else {
            switch (e.kind()) {
            case expr_kind::Local:      return e;
            case expr_kind::Meta:       return e;
            case expr_kind::Sort:       return visit_sort(e);
            case expr_kind::Var:        lean_unreachable();  // LCOV_EXCL_LINE
            case expr_kind::Constant:   return visit_constant(e);
            case expr_kind::Macro:      return visit_macro(e);
            case expr_kind::Lambda:     return visit_lambda(e);
            case expr_kind::Pi:         return visit_pi(e);
            case expr_kind::App:        return visit_app(e);
            }
            lean_unreachable(); // LCOV_EXCL_LINE
        }
    }

    expr visit(expr const & e) {
        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;
        expr r;
        if (is_explicit(e)) {
            r    = visit_core(get_explicit_arg(e));
        } else {
            r    = visit_core(e);
            if (!is_lambda(r)) {
                tag  g      = e.get_tag();
                expr r_type = whnf(infer_type(r));
                expr imp_arg;
                while (is_pi(r_type) && binding_info(r_type).is_implicit()) {
                    imp_arg = mk_meta(some_expr(binding_domain(r_type)), g);
                    r       = mk_app(r, imp_arg, g);
                    r_type  = whnf(instantiate(binding_body(r_type), imp_arg));
                }
            }
        }
        m_cache.insert(e, r);
        return r;
    }

    lazy_list<substitution> solve() {
        buffer<constraint> cs;
        cs.append(m_constraints);
        m_constraints.clear();
        // for (auto c : cs) { std::cout << "   " << c << "\n"; }
        return unify(m_env, cs.size(), cs.data(), m_ngen.mk_child(), m_plugin,
                     true, get_unifier_max_steps(m_ios.get_options()));
    }

    expr operator()(expr const & e) {
        // std::cout << "e: " << e << "\n";
        expr r  = visit(e);
        auto p  = solve().pull();
        lean_assert(p);
        // std::cout << "r: " << r << "\n";
        substitution s = p->first;
        // std::cout << "sol: " << s.instantiate_metavars_wo_jst(r) << "\n";
        return s.instantiate_metavars_wo_jst(r);
    }

    std::pair<expr, expr> operator()(expr const & t, expr const & v, name const & n) {
        // std::cout << "t:   " << t   << "\n";
        // std::cout << "v:   " << v   << "\n";
        expr r_t      = visit(t);
        // std::cout << "r_t: " << r_t << "\n";
        expr r_v      = visit(v);
        // std::cout << "r_v: " << r_v << "\n";
        expr r_v_type = infer_type(r_v);
        environment env = m_env;
        justification j = mk_justification(v, [=](formatter const & fmt, options const & o, substitution const & subst) {
                return pp_def_type_mismatch(fmt, env, o, n,
                                            subst.instantiate_metavars_wo_jst(r_t),
                                            subst.instantiate_metavars_wo_jst(r_v_type));
            });
        if (!m_tc.is_def_eq(r_v_type, r_t, j)) {
            throw_kernel_exception(env, v,
                                   [=](formatter const & fmt, options const & o) {
                                       return pp_def_type_mismatch(fmt, env, o, n, r_t, r_v_type);
                                   });
        }

        auto p  = solve().pull();
        lean_assert(p);
        substitution s = p->first;
        // std::cout << "sol: " << s.instantiate_metavars_wo_jst(r_t) << "\n";
        // std::cout << "     " << s.instantiate_metavars_wo_jst(r_v) << "\n";
        return mk_pair(s.instantiate_metavars_wo_jst(r_t),
                       s.instantiate_metavars_wo_jst(r_v));
    }
};

static name g_tmp_prefix = name::mk_internal_unique_name();

expr elaborate(environment const & env, io_state const & ios, expr const & e, name_generator const & ngen,
               substitution const & s, list<parameter> const & ctx) {
    return elaborator(env, ios, ngen, s, ctx)(e);
}

expr elaborate(environment const & env, io_state const & ios, expr const & e) {
    return elaborate(env, ios, e, name_generator(g_tmp_prefix), substitution(), list<parameter>());
}

std::pair<expr, expr> elaborate(environment const & env, io_state const & ios, name const & n, expr const & t, expr const & v) {
    return elaborator(env, ios, name_generator(g_tmp_prefix))(t, v, n);
}
}
