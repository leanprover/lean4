/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name.h"
#include "util/sstream.h"
#include "util/name_map.h"
#include "kernel/environment.h"
#include "kernel/builtin.h"
#include "library/hidden_defs.h"
#include "library/kernel_bindings.h"

namespace lean {
struct hidden_defs_extension : public environment_extension {
    typedef name_map<bool> hidden_defs;
    hidden_defs m_hidden_defs;

    hidden_defs_extension const * get_parent() const {
        return environment_extension::get_parent<hidden_defs_extension>();
    }

    bool is_hidden(name const & n) const {
        auto it = m_hidden_defs.find(n);
        if (it != m_hidden_defs.end())
            return it->second;
        hidden_defs_extension const * parent = get_parent();
        return parent && parent->is_hidden(n);
    }

    void set_hidden_flag(name const & d, bool f) {
        m_hidden_defs[d] = f;
    }
};

struct hidden_defs_extension_initializer {
    unsigned m_extid;
    hidden_defs_extension_initializer() {
        m_extid = environment_cell::register_extension([](){ return std::unique_ptr<environment_extension>(new hidden_defs_extension()); });
    }
};

static hidden_defs_extension_initializer g_hidden_defs_extension_initializer;

static hidden_defs_extension const & to_ext(ro_environment const & env) {
    return env->get_extension<hidden_defs_extension>(g_hidden_defs_extension_initializer.m_extid);
}

static hidden_defs_extension & to_ext(environment const & env) {
    return env->get_extension<hidden_defs_extension>(g_hidden_defs_extension_initializer.m_extid);
}

bool is_hidden(ro_environment const & env, name const & d) {
    return to_ext(env).is_hidden(d);
}

void set_hidden_flag(environment const & env, name const & d, bool flag) {
    if (!env->get_object(d).is_definition())
        throw exception(sstream() << "'" << d << "' is not a definition");
    to_ext(env).set_hidden_flag(d, flag);
}

void hide_builtin(environment const & env) {
    for (auto c : { mk_implies_fn(), mk_iff_fn(), mk_not_fn(), mk_or_fn(), mk_and_fn(),
                mk_forall_fn(), mk_exists_fn(), mk_homo_eq_fn() })
        set_hidden_flag(env, const_name(c));
}

static int is_hidden(lua_State * L) {
    ro_shared_environment env(L, 1);
    lua_pushboolean(L, is_hidden(env, to_name_ext(L, 2)));
    return 1;
}

static int set_hidden_flag(lua_State * L) {
    int nargs = lua_gettop(L);
    rw_shared_environment env(L, 1);
    set_hidden_flag(env, to_name_ext(L, 2), nargs <= 2 ? true : lua_toboolean(L, 3));
    return 0;
}

void open_hidden_defs(lua_State * L) {
    SET_GLOBAL_FUN(is_hidden,       "is_hidden");
    SET_GLOBAL_FUN(set_hidden_flag, "set_hidden_flag");
}
}
