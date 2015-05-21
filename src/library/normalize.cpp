/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "util/name_generator.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "kernel/inductive/inductive.h"
#include "library/reducible.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"

namespace lean {
/**
   \brief unfold hints instruct the normalizer (and simplifier) that
   a function application. We have two kinds of hints:
   - unfold_c (f a_1 ... a_i ... a_n) should be unfolded
     when argument a_i is a constructor.
   - unfold_f (f a_1 ... a_i ... a_n) should be unfolded when it is fully applied.
   - constructor (f ...) should be unfolded when it is the major premise of a recursor-like operator
*/
struct unfold_hint_entry {
    enum kind {UnfoldC, UnfoldF, UnfoldM};
    kind     m_kind; //!< true if it is an unfold_c hint
    bool     m_add;  //!< add/remove hint
    name     m_decl_name;
    unsigned m_arg_idx;
    unfold_hint_entry():m_kind(UnfoldC), m_add(false), m_arg_idx(0) {}
    unfold_hint_entry(kind k, bool add, name const & n, unsigned idx):
        m_kind(k), m_add(add), m_decl_name(n), m_arg_idx(idx) {}
};

unfold_hint_entry mk_add_unfold_c_entry(name const & n, unsigned idx) { return unfold_hint_entry(unfold_hint_entry::UnfoldC, true, n, idx); }
unfold_hint_entry mk_erase_unfold_c_entry(name const & n) { return unfold_hint_entry(unfold_hint_entry::UnfoldC, false, n, 0); }
unfold_hint_entry mk_add_unfold_f_entry(name const & n) { return unfold_hint_entry(unfold_hint_entry::UnfoldF, true, n, 0); }
unfold_hint_entry mk_erase_unfold_f_entry(name const & n) { return unfold_hint_entry(unfold_hint_entry::UnfoldF, false, n, 0); }
unfold_hint_entry mk_add_constructor_entry(name const & n) { return unfold_hint_entry(unfold_hint_entry::UnfoldM, true, n, 0); }
unfold_hint_entry mk_erase_constructor_entry(name const & n) { return unfold_hint_entry(unfold_hint_entry::UnfoldM, false, n, 0); }

static name * g_unfold_hint_name = nullptr;
static std::string * g_key = nullptr;

struct unfold_hint_state {
    name_map<unsigned>  m_unfold_c;
    name_set            m_unfold_f;
    name_set            m_constructor;
};

struct unfold_hint_config {
    typedef unfold_hint_state state;
    typedef unfold_hint_entry entry;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        switch (e.m_kind) {
        case unfold_hint_entry::UnfoldC:
            if (e.m_add)
                s.m_unfold_c.insert(e.m_decl_name, e.m_arg_idx);
            else
                s.m_unfold_c.erase(e.m_decl_name);
            break;
        case unfold_hint_entry::UnfoldF:
            if (e.m_add)
                s.m_unfold_f.insert(e.m_decl_name);
            else
                s.m_unfold_f.erase(e.m_decl_name);
            break;
        case unfold_hint_entry::UnfoldM:
            if (e.m_add)
                s.m_constructor.insert(e.m_decl_name);
            else
                s.m_constructor.erase(e.m_decl_name);
            break;
        }
    }
    static name const & get_class_name() {
        return *g_unfold_hint_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << static_cast<char>(e.m_kind) << e.m_add << e.m_decl_name << e.m_arg_idx;
    }
    static entry read_entry(deserializer & d) {
        char k;
        entry e;
        d >> k >> e.m_add >> e.m_decl_name >> e.m_arg_idx;
        e.m_kind = static_cast<unfold_hint_entry::kind>(k);
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.m_decl_name.hash());
    }
};

template class scoped_ext<unfold_hint_config>;
typedef scoped_ext<unfold_hint_config> unfold_hint_ext;

environment add_unfold_c_hint(environment const & env, name const & n, unsigned idx, bool persistent) {
    declaration const & d = env.get(n);
    if (!d.is_definition())
        throw exception("invalid unfold-c hint, declaration must be a non-opaque definition");
    return unfold_hint_ext::add_entry(env, get_dummy_ios(), mk_add_unfold_c_entry(n, idx), persistent);
}

optional<unsigned> has_unfold_c_hint(environment const & env, name const & d) {
    unfold_hint_state const & s = unfold_hint_ext::get_state(env);
    if (auto it = s.m_unfold_c.find(d))
        return optional<unsigned>(*it);
    else
        return optional<unsigned>();
}

environment erase_unfold_c_hint(environment const & env, name const & n, bool persistent) {
    return unfold_hint_ext::add_entry(env, get_dummy_ios(), mk_erase_unfold_c_entry(n), persistent);
}

environment add_unfold_f_hint(environment const & env, name const & n, bool persistent) {
    declaration const & d = env.get(n);
    if (!d.is_definition())
        throw exception("invalid unfold-f hint, declaration must be a non-opaque definition");
    return unfold_hint_ext::add_entry(env, get_dummy_ios(), mk_add_unfold_f_entry(n), persistent);
}

bool has_unfold_f_hint(environment const & env, name const & d) {
    unfold_hint_state const & s = unfold_hint_ext::get_state(env);
    return s.m_unfold_f.contains(d);
}

environment erase_unfold_f_hint(environment const & env, name const & n, bool persistent) {
    return unfold_hint_ext::add_entry(env, get_dummy_ios(), mk_erase_unfold_f_entry(n), persistent);
}

environment add_constructor_hint(environment const & env, name const & n, bool persistent) {
    env.get(n);
    return unfold_hint_ext::add_entry(env, get_dummy_ios(), mk_add_constructor_entry(n), persistent);
}

bool has_constructor_hint(environment const & env, name const & d) {
    unfold_hint_state const & s = unfold_hint_ext::get_state(env);
    return s.m_constructor.contains(d);
}

environment erase_constructor_hint(environment const & env, name const & n, bool persistent) {
    return unfold_hint_ext::add_entry(env, get_dummy_ios(), mk_erase_constructor_entry(n), persistent);
}

void initialize_normalize() {
    g_unfold_hint_name = new name("unfold-hints");
    g_key = new std::string("unfoldh");
    unfold_hint_ext::initialize();
}

void finalize_normalize() {
    unfold_hint_ext::finalize();
    delete g_unfold_hint_name;
    delete g_key;
}

class normalize_fn {
    type_checker   &                  m_tc;
    name_generator                    m_ngen;
    std::function<bool(expr const &)> m_pred;  // NOLINT
    bool                              m_save_cnstrs;
    constraint_seq                    m_cnstrs;
    bool                              m_use_eta;
    bool                              m_eval_nested_prop;

    environment const & env() const { return m_tc.env(); }

    expr normalize_binding(expr const & e) {
        expr d = normalize(binding_domain(e));
        expr l = mk_local(m_ngen.next(), binding_name(e), d, binding_info(e));
        expr b = abstract(normalize(instantiate(binding_body(e), l)), l);
        return update_binding(e, d, b);
    }

    optional<unsigned> has_unfold_c_hint(expr const & f) {
        if (!is_constant(f))
            return optional<unsigned>();
        return ::lean::has_unfold_c_hint(env(), const_name(f));
    }

    bool has_unfold_f_hint(expr const & f) {
        return is_constant(f) &&  ::lean::has_unfold_f_hint(env(), const_name(f));
    }

    optional<expr> is_constructor_like(expr const & e) {
        if (is_constructor_app(env(), e))
            return some_expr(e);
        expr const & f = get_app_fn(e);
        if (is_constant(f) && has_constructor_hint(env(), const_name(f))) {
            if (auto r = unfold_term(env(), e))
                return r;
            else
                return some_expr(e);
        } else {
            return none_expr();
        }
    }

    optional<expr> unfold_recursor_core(expr const & f, unsigned idx, buffer<expr> & args, bool is_rec) {
        if (idx < args.size()) {
            expr & arg = args[args.size() - idx - 1];
            if (optional<expr> new_arg = is_constructor_like(arg)) {
                flet<expr> set_arg(arg, *new_arg);
                expr new_app = mk_rev_app(f, args);
                if (is_rec)
                    return some_expr(normalize(new_app));
                else if (optional<expr> r = unfold_app(env(), new_app))
                    return some_expr(normalize(*r));
            }
        }
        return none_expr();
    }

    optional<expr> unfold_recursor_like(expr const & f, unsigned idx, buffer<expr> & args) {
        return unfold_recursor_core(f, idx, args, false);
    }

    optional<expr> unfold_recursor_major(expr const & f, unsigned idx, buffer<expr> & args) {
        return unfold_recursor_core(f, idx, args, true);
    }

    expr normalize_app(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f = get_app_rev_args(e, args);
        for (expr & a : args) {
            expr new_a = a;
            if (m_eval_nested_prop || !m_tc.is_prop(m_tc.infer(a).first).first)
                 new_a = normalize(a);
            if (new_a != a)
                modified = true;
            a = new_a;
        }
        if (has_unfold_f_hint(f)) {
            if (!is_pi(m_tc.whnf(m_tc.infer(e).first).first)) {
                if (optional<expr> r = unfold_app(env(), mk_rev_app(f, args)))
                    return normalize(*r);
            }
        }
        if (auto idx = has_unfold_c_hint(f)) {
            if (auto r = unfold_recursor_like(f, *idx, args))
                return *r;
        }
        if (is_constant(f)) {
            if (auto idx = inductive::get_elim_major_idx(env(), const_name(f))) {
                if (auto r = unfold_recursor_major(f, *idx, args))
                    return *r;
            }
        }
        if (!modified)
            return e;
        expr r = mk_rev_app(f, args);
        if (is_constant(f) && inductive::is_elim_rule(env(), const_name(f))) {
            return normalize(r);
        } else {
            return r;
        }
    }

    expr try_eta(expr const & e) {
        lean_assert(is_lambda(e));
        expr const & b = binding_body(e);
        if (is_lambda(b)) {
            expr new_b = try_eta(b);
            if (is_eqp(b, new_b)) {
                return e;
            } else if (is_app(new_b) && is_var(app_arg(new_b), 0) && !has_free_var(app_fn(new_b), 0)) {
                return lower_free_vars(app_fn(new_b), 1);
            } else {
                return update_binding(e, binding_domain(e), new_b);
            }
        } else if (is_app(b) && is_var(app_arg(b), 0) && !has_free_var(app_fn(b), 0)) {
            return lower_free_vars(app_fn(b), 1);
        } else {
            return e;
        }
    }

    expr normalize(expr e) {
        check_system("normalize");
        if (!m_pred(e))
            return e;
        auto w = m_tc.whnf(e);
        e = w.first;
        if (m_save_cnstrs)
            m_cnstrs += w.second;
        switch (e.kind()) {
        case expr_kind::Var:  case expr_kind::Constant: case expr_kind::Sort:
        case expr_kind::Meta: case expr_kind::Local: case expr_kind::Macro:
            return e;
        case expr_kind::Lambda: {
            e = normalize_binding(e);
            if (m_use_eta)
                return try_eta(e);
            else
                return e;
        }
        case expr_kind::Pi:
            return normalize_binding(e);
        case expr_kind::App:
            return normalize_app(e);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

public:
    normalize_fn(type_checker & tc, bool save, bool eta, bool nested_prop = true):
        m_tc(tc), m_ngen(m_tc.mk_ngen()),
        m_pred([](expr const &) { return true; }),
        m_save_cnstrs(save), m_use_eta(eta), m_eval_nested_prop(nested_prop) {
        if (!is_standard(env()))
            m_eval_nested_prop = true;
    }

    normalize_fn(type_checker & tc, std::function<bool(expr const &)> const & fn, bool eta, bool nested_prop = true): // NOLINT
        m_tc(tc), m_ngen(m_tc.mk_ngen()),
        m_pred(fn), m_save_cnstrs(true), m_use_eta(eta), m_eval_nested_prop(nested_prop) {
        if (!is_standard(env()))
            m_eval_nested_prop = true;
    }

    expr operator()(expr const & e) {
        m_cnstrs = constraint_seq();
        return normalize(e);
    }

    expr operator()(level_param_names const & ls, expr const & e) {
        m_cnstrs = constraint_seq();
        return m_tc.with_params(ls, [&]() {
                return normalize(e);
            });
    }

    constraint_seq get_cnstrs() const { return m_cnstrs; }
};

expr normalize(environment const & env, expr const & e, bool eta) {
    auto tc          = mk_type_checker(env);
    bool save_cnstrs = false;
    return normalize_fn(*tc, save_cnstrs, eta)(e);
}

expr normalize(environment const & env, level_param_names const & ls, expr const & e, bool eta) {
    auto tc          = mk_type_checker(env);
    bool save_cnstrs = false;
    return normalize_fn(*tc, save_cnstrs, eta)(ls, e);
}

expr normalize(type_checker & tc, expr const & e, bool eta) {
    bool save_cnstrs = false;
    return normalize_fn(tc, save_cnstrs, eta)(e);
}

expr normalize(type_checker & tc, level_param_names const & ls, expr const & e, bool eta, bool eval_nested_prop) {
    bool save_cnstrs = false;
    return normalize_fn(tc, save_cnstrs, eta, eval_nested_prop)(ls, e);
}

expr normalize(type_checker & tc, expr const & e, constraint_seq & cs, bool eta) {
    bool save_cnstrs = false;
    normalize_fn fn(tc, save_cnstrs, eta);
    expr r = fn(e);
    cs += fn.get_cnstrs();
    return r;
}

expr normalize(type_checker & tc, expr const & e, std::function<bool(expr const &)> const & pred, // NOLINT
               constraint_seq & cs, bool eta) {
    normalize_fn fn(tc, pred, eta);
    expr r = fn(e);
    cs += fn.get_cnstrs();
    return r;
}
}
