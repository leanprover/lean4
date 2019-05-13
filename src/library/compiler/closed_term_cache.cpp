/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/module.h"
#include "library/util.h"

namespace lean {
/* Cache closed term => global constant.
   TODO(Leo): use the to be implemented new module system. */
struct closed_term_ext : public environment_extension {
    typedef rb_expr_map<name> cache;
    cache m_cache;
};

struct closed_term_ext_reg {
    unsigned m_ext_id;
    closed_term_ext_reg() { m_ext_id = environment::register_extension(new closed_term_ext()); }
};

static closed_term_ext_reg * g_ext = nullptr;
static closed_term_ext const & get_extension(environment const & env) {
    return static_cast<closed_term_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, closed_term_ext const & ext) {
    return env.update(g_ext->m_ext_id, new closed_term_ext(ext));
}

/* Support for old module manager.
   Remark: this code will be deleted in the future */
struct ct_cache_modification : public modification {
    LEAN_MODIFICATION("ctc")

    expr      m_expr;
    name      m_name;

    ct_cache_modification(expr const & e, name const & n): m_expr(e), m_name(n) {}

    void perform(environment & env) const override {
        closed_term_ext ext = get_extension(env);
        ext.m_cache.insert(m_expr, m_name);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_expr << m_name;
    }

    static modification* deserialize(deserializer & d) {
        expr e; name n;
        d >> e >> n;
        return new ct_cache_modification(e, n);
    }
};

optional<name> get_closed_term_name(environment const & env, expr const & e) {
    lean_assert(!has_fvar(e));
    lean_assert(!has_loose_bvars(e));
    closed_term_ext const & ext = get_extension(env);
    if (name const * c = ext.m_cache.find(e)) {
        return optional<name>(*c);
    } else {
        return optional<name>();
    }
}

environment cache_closed_term_name(environment const & env, expr const & e, name const & n) {
    closed_term_ext ext = get_extension(env);
    ext.m_cache.insert(e, n);
    environment new_env = module::add(env, new ct_cache_modification(e, n));
    return update(new_env, ext);
}

void initialize_closed_term_cache() {
    g_ext = new closed_term_ext_reg();
    ct_cache_modification::init();
}

void finalize_closed_term_cache() {
    ct_cache_modification::finalize();
    delete g_ext;
}
}
