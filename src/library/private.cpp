/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/hash.h"
#include "library/private.h"
#include "library/module.h"
#include "library/kernel_bindings.h"

namespace lean {
struct private_ext : public environment_extension {
    unsigned       m_counter;
    name_map<name> m_inv_map;  // map: hidden-name -> user-name
    private_ext():m_counter(0) {}
};

struct private_ext_reg {
    unsigned m_ext_id;
    private_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<private_ext>()); }
};

static private_ext_reg * g_ext = nullptr;
static private_ext const & get_extension(environment const & env) {
    return static_cast<private_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, private_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<private_ext>(ext));
}

static name * g_private = nullptr;
static std::string * g_prv_key = nullptr;

// Make sure the mapping "hidden-name r ==> user-name n" is preserved when we close sections and
// export .olean files.
static environment preserve_private_data(environment const & env, name const & r, name const & n) {
    return module::add(env, *g_prv_key, [=](environment const &, serializer & s) { s << n << r; });
}

pair<environment, name> add_private_name(environment const & env, name const & n, optional<unsigned> const & extra_hash) {
    private_ext ext = get_extension(env);
    unsigned h      = hash(n.hash(), ext.m_counter);
    if (extra_hash)
        h = hash(h, *extra_hash);
    name r = name(*g_private, h) + n;
    ext.m_inv_map.insert(r, n);
    ext.m_counter++;
    environment new_env = update(env, ext);
    new_env = preserve_private_data(new_env, r, n);
    return mk_pair(new_env, r);
}

static void private_reader(deserializer & d, shared_environment & senv,
                           std::function<void(asynch_update_fn const &)> &,
                           std::function<void(delayed_update_fn const &)> &) {
    name n, h;
    d >> n >> h;
    senv.update([=](environment const & env) -> environment {
            private_ext ext = get_extension(env);
            // we restore only the mapping hidden-name -> user-name (for pretty printing purposes)
            ext.m_inv_map.insert(h, n);
            ext.m_counter++;
            return update(env, ext);
        });
}

optional<name> hidden_to_user_name(environment const & env, name const & n) {
    auto it = get_extension(env).m_inv_map.find(n);
    return it ? optional<name>(*it) : optional<name>();
}

static int add_private_name(lua_State * L) {
    int nargs = lua_gettop(L);
    optional<unsigned> h;
    if (nargs > 2)
        h = lua_tonumber(L, 3);
    auto p = add_private_name(to_environment(L, 1), to_name_ext(L, 2), h);
    push_environment(L, p.first);
    push_name(L, p.second);
    return 2;
}

static int hidden_to_user_name(lua_State * L) {
    return push_optional_name(L, hidden_to_user_name(to_environment(L, 1), to_name_ext(L, 2)));
}

void open_private(lua_State * L) {
    SET_GLOBAL_FUN(add_private_name,    "add_private_name");
    SET_GLOBAL_FUN(hidden_to_user_name, "hidden_to_user_name");
}

void initialize_private() {
    g_ext     = new private_ext_reg();
    g_private = new name("private");
    g_prv_key = new std::string("prv");
    register_module_object_reader(*g_prv_key, private_reader);
}

void finalize_private() {
    delete g_prv_key;
    delete g_private;
    delete g_ext;
}
}
