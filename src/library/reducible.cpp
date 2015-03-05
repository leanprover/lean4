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

void reducible_state::add(reducible_entry const & e) {
    m_status.insert(e.m_name, e.m_status);
}

reducible_status reducible_state::get_status(name const & n) const {
    if (auto it = m_status.find(n))
        return *it;
    else
        return reducible_status::Semireducible;
}

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

reducible_status get_reducible_status(environment const & env, name const & n) {
    reducible_state const & s = reducible_ext::get_state(env);
    return s.get_status(n);
}

bool is_at_least_quasireducible(environment const & env, name const & n) {
    reducible_status r = get_reducible_status(env, n);
    return r == reducible_status::Reducible || r == reducible_status::Quasireducible;
}

unfold_reducible_converter::unfold_reducible_converter(environment const & env, bool relax_main_opaque, bool memoize):
    default_converter(env, relax_main_opaque, memoize) {
    m_state = reducible_ext::get_state(env);
}

bool unfold_reducible_converter::is_opaque(declaration const & d) const {
    auto r = m_state.get_status(d.get_name());
    if (r != reducible_status::Reducible) return true;
    return default_converter::is_opaque(d);
}

unfold_quasireducible_converter::unfold_quasireducible_converter(environment const & env, bool relax_main_opaque, bool memoize):
    default_converter(env, relax_main_opaque, memoize) {
    m_state = reducible_ext::get_state(env);
}

bool unfold_quasireducible_converter::is_opaque(declaration const & d) const {
    auto r = m_state.get_status(d.get_name());
    if (r != reducible_status::Reducible && r != reducible_status::Quasireducible) return true;
    return default_converter::is_opaque(d);
}

unfold_semireducible_converter::unfold_semireducible_converter(environment const & env, bool relax_main_opaque, bool memoize):
    default_converter(env, relax_main_opaque, memoize) {
    m_state = reducible_ext::get_state(env);
}

bool unfold_semireducible_converter::is_opaque(declaration const & d) const {
    auto r = m_state.get_status(d.get_name());
    if (r == reducible_status::Irreducible) return true;
    return default_converter::is_opaque(d);
}

std::unique_ptr<type_checker> mk_type_checker(environment const & env, name_generator const & ngen,
                                              bool relax_main_opaque, reducible_behavior rb,
                                              bool memoize) {
    switch (rb) {
    case UnfoldReducible:
        return std::unique_ptr<type_checker>(new type_checker(env, ngen,
               std::unique_ptr<converter>(new unfold_reducible_converter(env, relax_main_opaque, memoize))));
    case UnfoldQuasireducible:
        return std::unique_ptr<type_checker>(new type_checker(env, ngen,
               std::unique_ptr<converter>(new unfold_quasireducible_converter(env, relax_main_opaque, memoize))));
    case UnfoldSemireducible:
        return std::unique_ptr<type_checker>(new type_checker(env, ngen,
               std::unique_ptr<converter>(new unfold_semireducible_converter(env, relax_main_opaque, memoize))));
    }
    lean_unreachable();
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
    return mk_reducible_checker_core(L, UnfoldReducible);
}

static int mk_non_irreducible_type_checker(lua_State * L) {
    return mk_reducible_checker_core(L, UnfoldSemireducible);
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
    SET_ENUM("Reducible",      reducible_status::Reducible);
    SET_ENUM("QuasiReducible", reducible_status::Quasireducible);
    SET_ENUM("SemiReducible",  reducible_status::Semireducible);
    SET_ENUM("Irreducible",    reducible_status::Irreducible);
    lua_setglobal(L, "reducible_status");
    SET_GLOBAL_FUN(set_reducible,                   "set_reducible");
    SET_GLOBAL_FUN(mk_opaque_type_checker,          "opaque_type_checker");
    SET_GLOBAL_FUN(mk_non_irreducible_type_checker, "non_irreducible_type_checker");
    SET_GLOBAL_FUN(mk_reducible_type_checker,       "reducible_type_checker");
}
}
