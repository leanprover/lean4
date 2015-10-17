/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lbool.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/normalize.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/replace_visitor.h"
#include "library/class_instance_resolution.h"

#ifndef LEAN_DEFAULT_CLASS_UNIQUE_CLASS_INSTANCES
#define LEAN_DEFAULT_CLASS_UNIQUE_CLASS_INSTANCES false
#endif

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
typedef std::shared_ptr<ci_type_inference> ci_type_inference_ptr;

static name * g_class_unique_class_instances = nullptr;
static name * g_class_trace_instances        = nullptr;
static name * g_class_instance_max_depth     = nullptr;
static name * g_class_trans_instances        = nullptr;
static name * g_prefix1                      = nullptr;
static name * g_prefix2                      = nullptr;

static ci_type_inference_factory * g_default_factory = nullptr;

LEAN_THREAD_PTR(ci_type_inference_factory, g_factory);
LEAN_THREAD_PTR(io_state,                  g_ios);

bool get_class_unique_class_instances(options const & o) {
    return o.get_bool(*g_class_unique_class_instances, LEAN_DEFAULT_CLASS_UNIQUE_CLASS_INSTANCES);
}

bool get_class_trace_instances(options const & o) {
    return o.get_bool(*g_class_trace_instances, LEAN_DEFAULT_CLASS_TRACE_INSTANCES);
}

unsigned get_class_instance_max_depth(options const & o) {
    return o.get_unsigned(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH);
}

bool get_class_trans_instances(options const & o) {
    return o.get_bool(*g_class_trans_instances, LEAN_DEFAULT_CLASS_TRANS_INSTANCES);
}

class default_ci_type_inference : public ci_type_inference {
    type_checker_ptr m_tc;
public:
    default_ci_type_inference(environment const & env):
        m_tc(mk_type_checker(env, name_generator(*g_prefix1), UnfoldReducible)) {}

    virtual ~default_ci_type_inference() {}

    virtual expr whnf(expr const & e) {
        return m_tc->whnf(e).first;
    }

    virtual expr infer_type(expr const & e) {
        return m_tc->infer(e).first;
    }
};

std::shared_ptr<ci_type_inference> ci_type_inference_factory::operator()(environment const & env) const {
    return std::shared_ptr<ci_type_inference>(new default_ci_type_inference(env));
}

static ci_type_inference_factory & get_ci_factory() {
    return g_factory ? *g_factory : *g_default_factory;
}

struct cienv {
    typedef rb_map<unsigned, level, unsigned_cmp> uassignment;
    typedef rb_map<unsigned, expr,  unsigned_cmp> eassignment;

    environment            m_env;
    ci_type_inference_ptr  m_tc_ptr;
    expr_struct_map<expr>  m_cache;
    name_generator         m_ngen;
    name_predicate         m_not_reducible_pred;

    list<expr>             m_ctx;
    buffer<expr>           m_local_instances;

    unsigned               m_next_uvar;
    unsigned               m_next_mvar;

    struct state {
        list<expr>   m_stack; // stack of meta-variables that need to be synthesized;
        uassignment  m_uassignment;
        eassignment  m_eassignment;
    };

    state                  m_state; // active state

    struct choice {
        list<expr>              m_local_instances;
        list<name>              m_trans_instances;
        list<name>              m_instances;
        state                   m_state;
    };

    list<choice>           m_choices;

    bool                   m_multiple_instances;

    // configuration
    bool                   m_unique_instances;
    unsigned               m_max_depth;
    bool                   m_trans_instances;
    bool                   m_trace_instances;

    cienv(bool multiple_instances = false):
        m_ngen(*g_prefix2),
        m_next_uvar(0),
        m_next_mvar(0),
        m_multiple_instances(multiple_instances) {}

    bool is_not_reducible(name const & n) const {
        return m_not_reducible_pred(n);
    }

    void reset_cache() {
        m_ctx = list<expr>();
        expr_struct_map<expr> fresh;
        fresh.swap(m_cache);
    }

    optional<expr> check_cache(expr const & type) const {
        if (m_multiple_instances) {
            // We do not cache results when multiple instances have to be generated.
            return none_expr();
        }
        auto it = m_cache.find(type);
        if (it != m_cache.end())
            return some_expr(it->second);
        else
            return none_expr();
    }

    void cache_result(expr const & type, expr const & inst) {
        if (m_multiple_instances) {
            // We do not cache results when multiple instances have to be generated.
            return;
        }
        m_cache.insert(mk_pair(type, inst));
    }

    void set_options(options const & o) {
        bool unique_instances = get_class_unique_class_instances(o);
        unsigned max_depth    = get_class_instance_max_depth(o);
        bool trans_instances  = get_class_trans_instances(o);
        bool trace_instances  = get_class_trace_instances(o);

        if (m_unique_instances != unique_instances ||
            m_max_depth        != max_depth        ||
            m_trans_instances  != trans_instances  ||
            m_trace_instances  != trace_instances) {
            reset_cache();
        }
        m_unique_instances = unique_instances;
        m_max_depth        = max_depth;
        m_trans_instances  = trans_instances;
        m_trace_instances  = trace_instances;
    }

    void set_env(environment const & env) {
        if (!m_env.is_descendant(m_env) || !m_env.is_descendant(env)) {
            m_env                = env;
            m_not_reducible_pred = mk_not_reducible_pred(m_env);
            m_tc_ptr             = nullptr;
            reset_cache();
        }

        if (!m_tc_ptr) {
            ci_type_inference_factory & factory = get_ci_factory();
            m_tc_ptr = factory(m_env);
        }
    }

    expr whnf(expr const & e) {
        return m_tc_ptr->whnf(e);
    }

    expr infer_type(expr const & e) {
        return m_tc_ptr->infer_type(e);
    }

    bool is_prop(expr const & e) {
        if (m_env.impredicative()) {
            expr t   = whnf(infer_type(e));
            return t == mk_Prop();
        } else {
            return false;
        }
    }

    name mk_fresh_name() {
        return m_ngen.next();
    }

    expr mk_local(expr const & type) {
        return lean::mk_local(mk_fresh_name(), type);
    }

    /** \brief If the constant \c e is a class, return its name */
    optional<name> constant_is_class(expr const & e) {
        name const & cls_name = const_name(e);
        if (lean::is_class(m_env, cls_name)) {
            return optional<name>(cls_name);
        } else {
            return optional<name>();
        }
    }

    optional<name> is_full_class(expr type) {
        type = whnf(type);
        if (is_pi(type)) {
            return is_full_class(instantiate(binding_body(type), mk_local(binding_domain(type))));
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
    lbool is_quick_class(expr const & type, name & result) {
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
                } else if (is_not_reducible(const_name(*it))) {
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
                    } else if (is_not_reducible(const_name(f))) {
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
    optional<name> is_class(expr const & type) {
        name result;
        switch (is_quick_class(type, result)) {
        case l_true:  return optional<name>(result);
        case l_false: return optional<name>();
        case l_undef: break;
        }
        return is_full_class(type);
    }


    // Auxiliary method for set_ctx
    void set_local_instance(unsigned i, expr const & e) {
        lean_assert(i <= m_local_instances.size());
        if (i == m_local_instances.size()) {
            reset_cache();
            m_local_instances.push_back(e);
        } else if (e != m_local_instances[i]) {
            reset_cache();
            m_local_instances[i] = e;
        } else {
            // we don't need to reset the cache since this local instance
            // is equal to the one used in a previous call
        }
    }

    void set_ctx(list<expr> const & ctx) {
        if (is_eqp(m_ctx, ctx)) {
            // we can keep the cache because the local context
            // is still pointing to the same object.
            return;
        }
        m_ctx = ctx;
        unsigned i = 0;
        for (expr const & e : ctx) {
            // Remark: we use infer_type(e) instead of mlocal_type because we want to allow
            // customers (e.g., blast) of this class to store the type of local constants
            // in a different place.
            if (is_class(infer_type(e))) {
                set_local_instance(i, e);
                i++;
            }
        }
    }

    // Create an internal universal metavariable
    level mk_uvar() {
        unsigned idx = m_next_uvar;
        m_next_uvar++;
        return mk_meta_univ(name(*g_prefix2, idx));
    }

    // Return true iff \c l is an internal universe metavariable created by this module.
    static bool is_uvar(level const & l) {
        if (!is_meta(l))
            return false;
        name const & n = meta_id(l);
        return !n.is_atomic() && n.get_prefix() == *g_prefix2;
    }

    static unsigned uvar_idx(level const & l) {
        lean_assert(is_uvar(l));
        return meta_id(l).get_numeral();
    }

    level const * get_assignment(level const & u) const {
        return m_state.m_uassignment.find(uvar_idx(u));
    }

    bool is_assigned(level const & u) const {
        return get_assignment(u) != nullptr;
    }

    // Assign \c v to the universe metavariable \c u.
    void update_assignment(level const & u, level const & v) {
        m_state.m_uassignment.insert(uvar_idx(u), v);
    }

    // Assign \c v to the universe metavariable \c u.
    void assign(level const & u, level const & v) {
        lean_assert(!is_assigned(u));
        update_assignment(u, v);
    }

    // Create an internal metavariable.
    expr mk_mvar(expr const & type) {
        unsigned idx = m_next_mvar;
        m_next_mvar++;
        return mk_metavar(name(*g_prefix2, idx), type);
    }

    // Return true iff \c e is an internal metavariable created by this module.
    static bool is_mvar(expr const & e) {
        if (!is_metavar(e))
            return false;
        name const & n = mlocal_name(e);
        return !n.is_atomic() && n.get_prefix() == *g_prefix2;
    }

    static unsigned mvar_idx(expr const & m) {
        lean_assert(is_mvar(m));
        return mlocal_name(m).get_numeral();
    }

    expr const * get_assignment(expr const & m) const {
        return m_state.m_eassignment.find(mvar_idx(m));
    }

    bool is_assigned(expr const & m) const {
        return get_assignment(m) != nullptr;
    }

    void update_assignment(expr const & m, expr const & v) {
        m_state.m_eassignment.insert(mvar_idx(m), v);
    }

    // Assign \c v to the metavariable \c m.
    void assign(expr const & m, expr const & v) {
        lean_assert(!is_assigned(m));
        update_assignment(m, v);
    }

    bool is_def_eq(level const & l1, level const & l2) {
        if (is_equivalent(l1, l2)) {
            return true;
        } else {
            if (is_uvar(l1)) {
                if (auto v = get_assignment(l1)) {
                    return is_def_eq(*v, l2);
                } else {
                    assign(l1, l2);
                    return true;
                }
            }
            if (is_uvar(l2)) {
                if (auto v = get_assignment(l2)) {
                    return is_def_eq(l1, *v);
                } else {
                    assign(l2, l1);
                    return true;
                }
            }
        }
        return false;
    }

    bool is_def_eq(levels const & ls1, levels const & ls2) {
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
    expr subst_mvar(expr const & e) {
        buffer<expr> args;
        expr const & m   = get_app_args(e, args);
        lean_assert(is_mvar(m));
        expr const * v = get_assignment(m);
        lean_assert(v);
        return apply_beta(*v, args.size(), args.data());
    }

    bool has_assigned_uvar(level const & l) const {
        if (!has_meta(l))
            return false;
        if (m_state.m_uassignment.empty())
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

    bool has_assigned_uvar(levels const & ls) const {
        for (level const & l : ls) {
            if (has_assigned_uvar(l))
                return true;
        }
        return false;
    }

    bool has_assigned_uvar_mvar(expr const & e) const {
        if (!has_expr_metavar(e) && !has_univ_metavar(e))
            return false;
        if (m_state.m_eassignment.empty() && m_state.m_uassignment.empty())
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

    level instantiate_uvars(level const & l) {
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
        cienv & m_owner;

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
            lean_assert(is_mvar(m));
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
        }

        virtual expr visit_app(expr const & e) {
            buffer<expr> args;
            expr const & f = get_app_rev_args(e, args);
            if (is_mvar(f)) {
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
            if (!has_expr_metavar(e) || !has_univ_metavar(e))
                return e;
            else
                return replace_visitor::visit(e);
        }

    public:
        instantiate_uvars_mvars_fn(cienv & o):m_owner(o) {}

        expr operator()(expr const & e) { return visit(e); }
    };

    expr instantiate_uvars_mvars(expr const & e) {
        if (!has_assigned_uvar_mvar(e))
            return e;
        else
            return instantiate_uvars_mvars_fn(*this)(e);
    }

    /** \brief Given \c ma of the form <tt>?m t_1 ... t_n</tt>, (try to) assign
        ?m to (an abstraction of) v. Return true if success and false otherwise. */
    bool assign_mvar(expr const & ma, expr const & v) {
        buffer<expr> args;
        expr const & m = get_app_args(ma, args);
        buffer<expr> locals;
        for (expr const & arg : args) {
            if (!is_local(arg))
                break; // is not local
            if (std::any_of(locals.begin(), locals.end(), [&](expr const & local) {
                        return mlocal_name(local) == mlocal_name(arg); }))
                break; // duplicate local
            locals.push_back(arg);
        }
        lean_assert(is_mvar(m));
        expr new_v = instantiate_uvars_mvars(v);

        // We must check
        //   1. Any local constant occurring in new_v occurs in locals
        //   2. m does not occur in new_v
        bool ok = true;
        for_each(new_v, [&](expr const & e, unsigned) {
                if (!ok)
                    return false; // stop search
                if (is_local(e)) {
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
        if (!ok)
            return false;
        if (args.empty()) {
            // easy case
            assign(m, new_v);
            return true;
        } else if (args.size() == locals.size()) {
            assign(m, Fun(locals, new_v));
            return true;
        } else {
            // This case is imprecise since it is not a higher order pattern.
            // That the term \c ma is of the form (?m t_1 ... t_n) and the t_i's are not pairwise
            // distinct local constants.
            expr m_type = mlocal_type(m);
            for (unsigned i = 0; i < args.size(); i++) {
                m_type = whnf(m_type);
                if (!is_pi(m_type))
                    return false;
                lean_assert(i <= locals.size());
                if (i == locals.size())
                    locals.push_back(mk_local(binding_domain(m_type)));
                lean_assert(i < locals.size());
                m_type = instantiate(binding_body(m_type), locals[i]);
            }
            lean_assert(locals.size() == args.size());
            assign(m, Fun(locals, new_v));
            return true;
        }
    }

    bool is_def_eq_binding(expr e1, expr e2) {
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
                subst.push_back(mk_local(*var_e1_type));
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

    bool is_def_eq_app(expr const & e1, expr const & e2) {
        lean_assert(is_app(e1) && is_app(e2));
        buffer<expr> args1, args2;
        expr const & f1 = get_app_args(e1, args1);
        expr const & f2 = get_app_args(e2, args2);
        if (args1.size() != args2.size() || !is_def_eq_core(f1, f2))
            return false;
        for (unsigned i = 0; i < args1.size(); i++) {
            if (!is_def_eq_core(args1[i], args2[i]))
                return false;
        }
        return true;
    }

    bool is_def_eq_eta(expr const & e1, expr const & e2) {
        expr new_e1 = try_eta(e1);
        expr new_e2 = try_eta(e2);
        if (e1 != new_e1 || e2 != new_e2)
            return is_def_eq_core(new_e1, new_e2);
        return false;
    }

    bool is_def_eq_proof_irrel(expr const & e1, expr const & e2) {
        if (!m_env.prop_proof_irrel())
            return false;
        expr e1_type = infer_type(e1);
        expr e2_type = infer_type(e2);
        return is_prop(e1_type) && is_def_eq_core(e1_type, e2_type);
    }

    bool is_def_eq_core(expr const & e1, expr const & e2) {
        check_system("is_def_eq");
        if (e1 == e2)
            return true;
        expr const & f1 = get_app_fn(e1);
        if (is_mvar(f1)) {
            if (is_assigned(f1)) {
                return is_def_eq_core(subst_mvar(e1), e2);
            } else {
                return assign_mvar(e1, e2);
            }
        }
        expr const & f2 = get_app_fn(e2);
        if (is_mvar(f2)) {
            if (is_assigned(f2)) {
                return is_def_eq_core(e1, subst_mvar(e2));
            } else {
                return assign_mvar(e2, e1);
            }
        }
        expr e1_n = whnf(e1);
        expr e2_n = whnf(e2);
        if (e1 != e1_n || e2 != e2_n)
            return is_def_eq_core(e1_n, e2_n);
        if (e1.kind() == e2.kind()) {
            switch (e1.kind()) {
            case expr_kind::Lambda:
            case expr_kind::Pi:
                if (is_def_eq_binding(e1, e2))
                    return true;
                break;
            case expr_kind::Sort:
                if (is_def_eq(sort_level(e1), sort_level(e2)))
                    return true;
                break;
            case expr_kind::Meta:
            case expr_kind::Var:
                lean_unreachable(); // LCOV_EXCL_LINE
            case expr_kind::Local:
            case expr_kind::Macro:
                break;
            case expr_kind::Constant:
                if (const_name(e1) == const_name(e2) &&
                    is_def_eq(const_levels(e1), const_levels(e2)))
                    return true;
                break;
            case expr_kind::App:
                if (is_def_eq_app(e1, e2))
                    return true;
                break;
            }
        }
        if (is_def_eq_eta(e1, e2))
            return true;
        return is_def_eq_proof_irrel(e1, e2);
    }

    bool is_def_eq(expr const & e1, expr const & e2) {
        state saved_state = m_state;
        if (!is_def_eq_core(e1, e2)) {
            m_state = saved_state;
            return false;
        } else {
            return true;
        }
    }

    expr init_search(expr const & type) {
        m_state = state();
        expr m  = mk_mvar(type);
        m_state.m_stack = cons(m, m_state.m_stack);
        return m;
    }

    optional<expr> search() {
        // TODO(Leo):
        return none_expr();
    }

    optional<expr> operator()(environment const & env, options const & o, list<expr> const & ctx, expr const & type) {
        set_env(env);
        set_options(o);
        set_ctx(ctx);

        if (auto r = check_cache(type))
            return r;

        expr m = init_search(type);

        if (auto r = search()) {
            cache_result(type, *r);
            return r;
        } else {
            return none_expr();
        }
    }

    optional<expr> next() {
        if (!m_multiple_instances)
            return none_expr();

        // TODO(Leo): backtrack and search
        return none_expr();
    }
};

MK_THREAD_LOCAL_GET_DEF(cienv, get_cienv);

static void reset_cache() {
    get_cienv().reset_cache();
}

ci_type_inference_factory_scope::ci_type_inference_factory_scope(ci_type_inference_factory & factory):
    m_old(g_factory) {
    g_factory = &factory;
    reset_cache();
}

ci_type_inference_factory_scope::~ci_type_inference_factory_scope() {
    reset_cache();
    g_factory = m_old;
}

optional<expr> mk_class_instance(environment const & env, io_state const & ios, list<expr> const & ctx, expr const & e) {
    flet<io_state*> set_ios(g_ios, const_cast<io_state*>(&ios));
    return get_cienv()(env, ios.get_options(), ctx, e);
}

optional<expr> mk_class_instance(environment const & env, list<expr> const & ctx, expr const & e) {
    return mk_class_instance(env, get_dummy_ios(), ctx, e);
}

void initialize_class_instance_resolution() {
    g_prefix1                      = new name(name::mk_internal_unique_name());
    g_prefix2                      = new name(name::mk_internal_unique_name());
    g_class_unique_class_instances = new name{"class", "unique_instances"};
    g_class_trace_instances        = new name{"class", "trace_instances"};
    g_class_instance_max_depth     = new name{"class", "instance_max_depth"};
    g_class_trans_instances        = new name{"class", "trans_instances"};

    register_bool_option(*g_class_unique_class_instances,  LEAN_DEFAULT_CLASS_UNIQUE_CLASS_INSTANCES,
                         "(class) generate an error if there is more than one solution "
                         "for a class-instance resolution problem");

    register_bool_option(*g_class_trace_instances,  LEAN_DEFAULT_CLASS_TRACE_INSTANCES,
                         "(class) display messages showing the class-instances resolution execution trace");

    register_unsigned_option(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH,
                             "(class) max allowed depth in class-instance resolution");

    register_bool_option(*g_class_trans_instances,  LEAN_DEFAULT_CLASS_TRANS_INSTANCES,
                         "(class) use automatically derived instances from the transitive closure of "
                         "the structure instance graph");
    g_default_factory = new ci_type_inference_factory();
}

void finalize_class_instance_resolution() {
    delete g_default_factory;
    delete g_prefix1;
    delete g_prefix2;
    delete g_class_unique_class_instances;
    delete g_class_trace_instances;
    delete g_class_instance_max_depth;
    delete g_class_trans_instances;
}
}
