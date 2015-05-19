/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/name_set.h"
#include "library/protected.h"
#include "library/module.h"

namespace lean {
struct protected_ext : public environment_extension {
    name_set m_protected; // protected declarations
};

struct protected_ext_reg {
    unsigned m_ext_id;
    protected_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<protected_ext>()); }
};

static protected_ext_reg * g_ext = nullptr;
static protected_ext const & get_extension(environment const & env) {
    return static_cast<protected_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, protected_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<protected_ext>(ext));
}

static std::string * g_prt_key = nullptr;

environment add_protected(environment const & env, name const & n) {
    protected_ext ext = get_extension(env);
    ext.m_protected.insert(n);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_prt_key, [=](environment const &, serializer & s) { s << n; });
}

static void protected_reader(deserializer & d, shared_environment & senv,
                             std::function<void(asynch_update_fn const &)> &,
                             std::function<void(delayed_update_fn const &)> &) {
    name n;
    d >> n;
    senv.update([=](environment const & env) -> environment {
            protected_ext ext = get_extension(env);
            ext.m_protected.insert(n);
            return update(env, ext);
        });
}

bool is_protected(environment const & env, name const & n) {
    return get_extension(env).m_protected.contains(n);
}

name get_protected_shortest_name(name const & n) {
    if (n.is_atomic() || n.get_prefix().is_atomic()) {
        return n;
    } else {
        name new_prefix = n.get_prefix().replace_prefix(n.get_prefix().get_prefix(), name());
        return n.replace_prefix(n.get_prefix(), new_prefix);
    }
}

void initialize_protected() {
    g_ext     = new protected_ext_reg();
    g_prt_key = new std::string("prt");
    register_module_object_reader(*g_prt_key, protected_reader);
}

void finalize_protected() {
    delete g_prt_key;
    delete g_ext;
}
}
