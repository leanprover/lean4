/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {
struct fresh_constant_ext : public environment_extension {
    unsigned       m_counter;
    fresh_constant_ext():m_counter(1) {}
};

struct fresh_constant_ext_reg {
    unsigned m_ext_id;
    fresh_constant_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<fresh_constant_ext>()); }
};

static fresh_constant_ext_reg * g_ext = nullptr;
static fresh_constant_ext const & get_extension(environment const & env) {
    return static_cast<fresh_constant_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, fresh_constant_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<fresh_constant_ext>(ext));
}

pair<environment, name> mk_fresh_constant(environment const & env, char const * prefix) {
    lean_assert(prefix && prefix[0] == '_');
    name p(prefix);
    fresh_constant_ext ext = get_extension(env);
    while (true) {
        name r = p.append_after(ext.m_counter);
        ext.m_counter++;
        if (!env.find(r))
            return mk_pair(update(env, ext), r);
    }
}

pair<environment, name> mk_fresh_constant(environment const & env) {
    return mk_fresh_constant(env, "_aux");
}

void initialize_fresh_constant() {
    g_ext     = new fresh_constant_ext_reg();
}

void finalize_fresh_constant() {
    delete g_ext;
}
}
