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
#include "library/fingerprint.h"

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

struct private_modification : public modification {
    LEAN_MODIFICATION("prv")

    name m_name, m_real;

    private_modification() {}
    private_modification(name const & n, name const & h) : m_name(n), m_real(h) {}

    void perform(environment & env) const override {
        private_ext ext = get_extension(env);
        // we restore only the mapping hidden-name -> user-name (for pretty printing purposes)
        ext.m_inv_map.insert(m_real, m_name);
        ext.m_counter++;
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_name << m_real;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name n, h;
        d >> n >> h;
        return std::make_shared<private_modification>(n, h);
    }
};

// Make sure the mapping "hidden-name r ==> user-name n" is preserved when we close sections and
// export .olean files.
static environment preserve_private_data(environment const & env, name const & r, name const & n) {
    return module::add(env, std::make_shared<private_modification>(n, r));
}

pair<environment, name> add_private_name(environment const & env, name const & n, optional<unsigned> const & extra_hash) {
    private_ext ext = get_extension(env);
    unsigned h      = hash(n.hash(), ext.m_counter);
    uint64   f      = get_fingerprint(env);
    h               = hash(h, static_cast<unsigned>(f >> 32));
    h               = hash(h, static_cast<unsigned>(f));
    if (extra_hash)
        h = hash(h, *extra_hash);
    name r = name(*g_private, h) + n;
    ext.m_inv_map.insert(r, n);
    ext.m_counter++;
    environment new_env = update(env, ext);
    new_env = preserve_private_data(new_env, r, n);
    return mk_pair(new_env, r);
}

optional<name> hidden_to_user_name(environment const & env, name const & n) {
    auto it = get_extension(env).m_inv_map.find(n);
    return it ? optional<name>(*it) : optional<name>();
}

bool is_private(environment const & env, name const & n) {
    return static_cast<bool>(hidden_to_user_name(env, n));
}

pair<environment, name> mk_private_name(environment const & env, name const & c) {
    unsigned h = 31;
    if (auto pinfo = get_pos_info_provider()) {
        h = hash(pinfo->get_some_pos().first, pinfo->get_some_pos().second);
        char const * fname = pinfo->get_file_name();
        h = hash_str(strlen(fname), fname, h);
    }
    return add_private_name(env, c, optional<unsigned>(h));
}

void initialize_private() {
    g_ext     = new private_ext_reg();
    g_private = new name("_private");
    private_modification::init();
}

void finalize_private() {
    private_modification::finalize();
    delete g_private;
    delete g_ext;
}
}
