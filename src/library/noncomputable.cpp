/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/util.h"
#include "library/fingerprint.h"
#include "library/trace.h"
#include "library/quote.h"
#include "library/constants.h"
// TODO(Leo): move inline attribute declaration to library
#include "library/compiler/inliner.h"
namespace lean {
struct noncomputable_ext : public environment_extension {
    name_set m_noncomputable;
    noncomputable_ext() {}
};

struct noncomputable_ext_reg {
    unsigned m_ext_id;
    noncomputable_ext_reg() {
        m_ext_id = environment::register_extension(std::make_shared<noncomputable_ext>());
    }
};

static noncomputable_ext_reg * g_ext = nullptr;
static noncomputable_ext const & get_extension(environment const & env) {
    return static_cast<noncomputable_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, noncomputable_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<noncomputable_ext>(ext));
}

struct noncomputable_modification : public modification {
    LEAN_MODIFICATION("ncomp")

    name m_decl;

    noncomputable_modification() {}
    noncomputable_modification(name const & decl) : m_decl(decl) {}

    void perform(environment & env) const override {
        noncomputable_ext ext = get_extension(env);
        ext.m_noncomputable.insert(m_decl);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<noncomputable_modification>(read_name(d));
    }
};

// TODO(Leo): implement better support for extending this set of builtin constants
static bool is_builtin_extra(name const & n) {
    return
        n == get_io_core_name() ||
        n == get_monad_io_impl_name() ||
        n == get_monad_io_terminal_impl_name() ||
        n == get_monad_io_file_system_impl_name() ||
        n == get_monad_io_environment_impl_name() ||
        n == get_monad_io_process_impl_name() ||
        n == get_monad_io_random_impl_name();
}

static bool is_noncomputable(type_checker & tc, noncomputable_ext const & ext, name const & n) {
    environment const & env = tc.env();
    if (ext.m_noncomputable.contains(n))
        return true;
    declaration const & d = env.get(n);
    if (!d.is_trusted()) {
        return false; /* ignore nontrusted definitions */
    } else if (d.is_axiom() && !tc.is_prop(d.get_type())) {
        return true;
    } else if (d.is_constant_assumption()) {
        return !env.is_builtin(d.get_name()) && !tc.is_prop(d.get_type()) && !is_builtin_extra(d.get_name());
    } else {
        return false;
    }
}

bool is_noncomputable(environment const & env, name const & n) {
    type_checker tc(env);
    auto ext = get_extension(env);
    return is_noncomputable(tc, ext, n);
}

bool is_marked_noncomputable(environment const & env, name const & n) {
    auto ext = get_extension(env);
    return ext.m_noncomputable.contains(n);
}

environment mark_noncomputable(environment const & env, name const & n) {
    auto ext = get_extension(env);
    ext.m_noncomputable.insert(n);
    environment new_env = update(env, ext);
    return module::add(new_env, std::make_shared<noncomputable_modification>(n));
}

struct get_noncomputable_reason_fn {
    struct found {
        name m_reason;
        found(name const & r):m_reason(r) {}
    };

    type_checker &            m_tc;
    noncomputable_ext const & m_ext;
    expr_set                  m_cache;

    get_noncomputable_reason_fn(type_checker & tc):
        m_tc(tc), m_ext(get_extension(tc.env())) {
    }

    void visit_constant(expr const & e) {
        if (is_noncomputable(m_tc, m_ext, const_name(e)))
            throw found(const_name(e));
    }

    bool should_visit(expr const & e) {
        if (m_cache.find(e) != m_cache.end())
            return false;
        m_cache.insert(e);
        expr type = m_tc.whnf(m_tc.infer(e));
        if (m_tc.is_prop(type) || is_sort(type))
            return false;
        while (is_pi(type)) {
            expr l = mk_local(m_tc.next_name(), binding_name(type), binding_domain(type), binding_info(type));
            type = m_tc.whnf(instantiate(binding_body(type), l));
        }
        return !is_sort(type);
    }

    void visit_macro(expr const & e) {
        if (is_expr_quote(e) || is_pexpr_quote(e))
            return;
        if (should_visit(e)) {
            for (unsigned i = 0; i < macro_num_args(e); i++)
                visit(macro_arg(e, i));
        }
    }

    void visit_app(expr const & e) {
        if (should_visit(e)) {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            if (is_constant(fn) && is_inline(m_tc.env(), const_name(fn))) {
                if (auto new_e = unfold_app(m_tc.env(), e)) {
                    visit(*new_e);
                    return;
                }
            }
            visit(fn);
            for (expr const & arg : args)
                visit(arg);
        }
    }

    void visit_binding(expr const & _e) {
        if (should_visit(_e)) {
            buffer<expr> ls;
            expr e = _e;
            while (is_lambda(e) || is_pi(e)) {
                expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
                expr l = mk_local(m_tc.next_name(), binding_name(e), d, binding_info(e));
                ls.push_back(l);
                e = binding_body(e);
            }
            visit(instantiate_rev(e, ls.size(), ls.data()));
        }
    }

    void visit_let(expr const & e) {
        if (should_visit(e)) {
            visit(instantiate(let_body(e), let_value(e)));
        }
    }

    void visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Sort:      return;
        case expr_kind::Macro:     visit_macro(e);    return;
        case expr_kind::Constant:  visit_constant(e); return;
        case expr_kind::Var:       lean_unreachable();
        case expr_kind::Meta:      lean_unreachable();
        case expr_kind::Local:     return;
        case expr_kind::App:       visit_app(e);      return;
        case expr_kind::Lambda:    visit_binding(e);  return;
        case expr_kind::Pi:        visit_binding(e);  return;
        case expr_kind::Let:       visit_let(e);      return;
        }
    }

    void operator()(expr const & e) {
        visit(e);
    }
};

optional<name> get_noncomputable_reason(environment const & env, name const & n) {
    declaration const & d = env.get(n);
    if (!d.is_definition())
        return optional<name>();
    type_checker tc(env);
    if (tc.is_prop(d.get_type()))
        return optional<name>(); // definition is a proposition, then do nothing
    expr const & v = d.get_value();
    auto ext = get_extension(env);
    bool ok  = true;
    /* quick check */
    for_each(v, [&](expr const & e, unsigned) {
            if (!ok) return false; // stop the search
            if (is_constant(e) && is_noncomputable(tc, ext, const_name(e))) {
                ok = false;
            }
            return true;
        });
    if (ok) {
        return optional<name>();
    }
    /* expensive check */
    try {
        get_noncomputable_reason_fn proc(tc);
        proc(v);
        return optional<name>();
    } catch (get_noncomputable_reason_fn::found & r) {
        return optional<name>(r.m_reason);
    }
}

bool check_computable(environment const & env, name const & n) {
    return !get_noncomputable_reason(env, n);
}

void initialize_noncomputable() {
    g_ext           = new noncomputable_ext_reg();
    noncomputable_modification::init();
}

void finalize_noncomputable() {
    noncomputable_modification::finalize();
    delete g_ext;
}
}
