/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/scoped_ext.h"
#include "library/reducible.h"
#include "library/kernel_bindings.h"

namespace lean {
struct reducible_entry {
    reducible_status m_status;
    name             m_name;
    reducible_entry():m_status(reducible_status::Semireducible) {}
    reducible_entry(reducible_status s, name const & n):m_status(s), m_name(n) {}
};

struct reducible_state {
    name_set m_reducible_on;
    name_set m_reducible_off;

    void add(reducible_entry const & e) {
        switch (e.m_status) {
        case reducible_status::Reducible:
            m_reducible_on.insert(e.m_name);
            m_reducible_off.erase(e.m_name);
            break;
        case reducible_status::Irreducible:
            m_reducible_on.erase(e.m_name);
            m_reducible_off.insert(e.m_name);
            break;
        case reducible_status::Semireducible:
            m_reducible_on.erase(e.m_name);
            m_reducible_off.erase(e.m_name);
            break;
        }
    }
};

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct reducible_config {
    typedef reducible_state  state;
    typedef reducible_entry  entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.add(e);
    }
    static name const & get_class_name() {
         return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << static_cast<char>(e.m_status) << e.m_name;
    }
    static entry read_entry(deserializer & d) {
        entry e; char s;
        d >> s >> e.m_name;
        e.m_status = static_cast<reducible_status>(s);
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(static_cast<unsigned>(e.m_status), e.m_name.hash()));
    }
};

template class scoped_ext<reducible_config>;
typedef scoped_ext<reducible_config> reducible_ext;

static name * g_tmp_prefix = nullptr;

void initialize_reducible() {
    g_class_name = new name("reduce-hints");
    g_key        = new std::string("redu");
    g_tmp_prefix = new name(name::mk_internal_unique_name());
    reducible_ext::initialize();
}

void finalize_reducible() {
    reducible_ext::finalize();
    delete g_tmp_prefix;
    delete g_key;
    delete g_class_name;
}

static void check_declaration(environment const & env, name const & n) {
    declaration const & d = env.get(n);
    if (!d.is_definition())
        throw exception(sstream() << "invalid reducible command, '" << n << "' is not a definition");
    if (d.is_theorem())
        throw exception(sstream() << "invalid reducible command, '" << n << "' is a theorem");
    if (d.is_opaque() && d.get_module_idx() != g_main_module_idx)
        throw exception(sstream() << "invalid reducible command, '" << n << "' is an opaque definition");
}

environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent) {
    check_declaration(env, n);
    return reducible_ext::add_entry(env, get_dummy_ios(), reducible_entry(s, n), persistent);
}

bool is_reducible_on(environment const & env, name const & n) {
    reducible_state const & s = reducible_ext::get_state(env);
    return s.m_reducible_on.contains(n);
}

bool is_reducible_off(environment const & env, name const & n) {
    reducible_state const & s = reducible_ext::get_state(env);
    return s.m_reducible_off.contains(n);
}

reducible_on_converter::reducible_on_converter(environment const & env, bool relax_main_opaque, bool memoize):
    default_converter(env, relax_main_opaque, memoize) {
    m_reducible_on = reducible_ext::get_state(env).m_reducible_on;
}

bool reducible_on_converter::is_opaque(declaration const & d) const {
    if (!m_reducible_on.contains(d.get_name())) return true;
    return default_converter::is_opaque(d);
}

reducible_off_converter::reducible_off_converter(environment const & env, bool relax_main_opaque, bool memoize):
    default_converter(env, relax_main_opaque, memoize) {
    m_reducible_off = reducible_ext::get_state(env).m_reducible_off;
}

bool reducible_off_converter::is_opaque(declaration const & d) const {
    if (m_reducible_off.contains(d.get_name())) return true;
    return default_converter::is_opaque(d);
}

std::unique_ptr<type_checker> mk_type_checker(environment const & env, name_generator const & ngen,
                                              bool relax_main_opaque, reducible_behavior rb,
                                              bool memoize) {
    if (rb == OpaqueIfNotReducibleOn) {
        return std::unique_ptr<type_checker>(new type_checker(env, ngen,
               std::unique_ptr<converter>(new reducible_on_converter(env, relax_main_opaque, memoize))));
    } else {
        return std::unique_ptr<type_checker>(new type_checker(env, ngen,
               std::unique_ptr<converter>(new reducible_off_converter(env, relax_main_opaque, memoize))));
    }
}

std::unique_ptr<type_checker> mk_type_checker(environment const & env, bool relax_main_opaque, reducible_behavior rb) {
    return mk_type_checker(env, name_generator(*g_tmp_prefix), relax_main_opaque, rb);
}

class opaque_converter : public default_converter {
public:
    opaque_converter(environment const & env): default_converter(env, true, true) {}
    virtual bool is_opaque(declaration const &) const { return true; }
};

std::unique_ptr<type_checker> mk_opaque_type_checker(environment const & env, name_generator const & ngen) {
    return std::unique_ptr<type_checker>(new type_checker(env, ngen,
                                                          std::unique_ptr<converter>(new opaque_converter(env))));
}

static int mk_opaque_type_checker(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        type_checker_ref r(mk_opaque_type_checker(get_global_environment(L), name_generator()));
        return push_type_checker_ref(L, r);
    } else if (nargs == 1) {
        type_checker_ref r(mk_opaque_type_checker(to_environment(L, 1), name_generator()));
        return push_type_checker_ref(L, r);
    } else {
        type_checker_ref r(mk_opaque_type_checker(to_environment(L, 1), to_name_generator(L, 2)));
        return push_type_checker_ref(L, r);
    }
}

static int mk_reducible_checker_core(lua_State * L, reducible_behavior rb) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        type_checker_ref r(mk_type_checker(get_global_environment(L), name_generator(), false, rb));
        return push_type_checker_ref(L, r);
    } else if (nargs == 1) {
        type_checker_ref r(mk_type_checker(to_environment(L, 1), name_generator(), false, rb));
        return push_type_checker_ref(L, r);
    } else {
        type_checker_ref r(mk_type_checker(to_environment(L, 1), to_name_generator(L, 2), false, rb));
        return push_type_checker_ref(L, r);
    }
}

static int mk_reducible_type_checker(lua_State * L) {
    return mk_reducible_checker_core(L, OpaqueIfNotReducibleOn);
}

static int mk_non_irreducible_type_checker(lua_State * L) {
    return mk_reducible_checker_core(L, OpaqueIfReducibleOff);
}

static int is_reducible_on(lua_State * L) {
    return push_boolean(L, is_reducible_on(to_environment(L, 1), to_name_ext(L, 2)));
}

static int is_reducible_off(lua_State * L) {
    return push_boolean(L, is_reducible_off(to_environment(L, 1), to_name_ext(L, 2)));
}

static int set_reducible(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3) {
        return push_environment(L, set_reducible(to_environment(L, 1), to_name_ext(L, 2),
                                                 static_cast<reducible_status>(lua_tonumber(L, 3))));
    } else {
        return push_environment(L, set_reducible(to_environment(L, 1), to_name_ext(L, 2),
                                                 static_cast<reducible_status>(lua_tonumber(L, 3)),
                                                 lua_toboolean(L, 4)));
    }
}

void open_reducible(lua_State * L) {
    lua_newtable(L);
    SET_ENUM("On",      reducible_status::Reducible);
    SET_ENUM("Off",     reducible_status::Irreducible);
    SET_ENUM("None",    reducible_status::Semireducible);
    lua_setglobal(L, "reducible_status");
    SET_GLOBAL_FUN(is_reducible_on,                 "is_reducible_on");
    SET_GLOBAL_FUN(is_reducible_off,                "is_reducible_off");
    SET_GLOBAL_FUN(set_reducible,                   "set_reducible");
    SET_GLOBAL_FUN(mk_opaque_type_checker,          "opaque_type_checker");
    SET_GLOBAL_FUN(mk_non_irreducible_type_checker, "non_irreducible_type_checker");
    SET_GLOBAL_FUN(mk_reducible_type_checker,       "reducible_type_checker");
}
}
