/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include <string>
#include "util/sstream.h"
#include "library/scoped_ext.h"
#include "library/kernel_bindings.h"

namespace lean {
typedef std::tuple<name, using_namespace_fn, export_namespace_fn, push_scope_fn, pop_scope_fn> entry;
typedef std::vector<entry> scoped_exts;
static scoped_exts * g_exts = nullptr;
static scoped_exts & get_exts() { return *g_exts; }

void register_scoped_ext(name const & c, using_namespace_fn use, export_namespace_fn ex, push_scope_fn push, pop_scope_fn pop) {
    get_exts().emplace_back(c, use, ex, push, pop);
}

struct scope_mng_ext : public environment_extension {
    name_set         m_namespace_set; // all namespaces registered in the system
    list<name>       m_namespaces;    // stack of namespaces/sections
    list<name>       m_headers;       // namespace/section header
    list<scope_kind> m_scope_kinds;
};

struct scope_mng_ext_reg {
    unsigned m_ext_id;
    scope_mng_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<scope_mng_ext>()); }
};

static scope_mng_ext_reg * g_ext = nullptr;
static scope_mng_ext const & get_extension(environment const & env) {
    return static_cast<scope_mng_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, scope_mng_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<scope_mng_ext>(ext));
}

name const & get_namespace(environment const & env) {
    scope_mng_ext const & ext = get_extension(env);
    return !is_nil(ext.m_namespaces) ? head(ext.m_namespaces) : name::anonymous();
}

list<name> const & get_namespaces(environment const & env) {
    return get_extension(env).m_namespaces;
}

bool in_section(environment const & env) {
    scope_mng_ext const & ext = get_extension(env);
    return !is_nil(ext.m_scope_kinds) && head(ext.m_scope_kinds) == scope_kind::Section;
}

void get_metaclasses(buffer<name> & r) {
    for (auto const & t : get_exts()) {
        name const & n = std::get<0>(t);
        if (std::find(r.begin(), r.end(), n) == r.end())
            r.push_back(n);
    }
}

bool is_metaclass(name const & n) {
    for (auto const & t : get_exts()) {
        if (std::get<0>(t) == n)
            return true;
    }
    return false;
}

environment using_namespace(environment const & env, io_state const & ios, name const & n, buffer<name> const & metaclasses) {
    environment r = env;
    for (auto const & t : get_exts()) {
        if (metaclasses.empty() ||
            std::find(metaclasses.begin(), metaclasses.end(), std::get<0>(t)) != metaclasses.end())
            r = std::get<1>(t)(r, ios, n);
    }
    return r;
}

static environment using_namespace(environment const & env, io_state const & ios, name const & n, name const & metaclass) {
    buffer<name> tmp;
    if (!metaclass.is_anonymous())
        tmp.push_back(metaclass);
    return using_namespace(env, ios, n, tmp);
}

environment using_namespace(environment const & env, io_state const & ios, name const & n) {
    buffer<name> metaclasses;
    return using_namespace(env, ios, n, metaclasses);
}

environment export_namespace(environment const & env, io_state const & ios, name const & n, buffer<name> const & metaclasses) {
    environment r = env;
    for (auto const & t : get_exts()) {
        if (metaclasses.empty() ||
            std::find(metaclasses.begin(), metaclasses.end(), std::get<0>(t)) != metaclasses.end())
            r = std::get<2>(t)(r, ios, n);
    }
    return r;
}

environment export_namespace(environment const & env, io_state const & ios, name const & n) {
    buffer<name> metaclasses;
    return export_namespace(env, ios, n, metaclasses);
}

optional<name> to_valid_namespace_name(environment const & env, name const & n) {
    scope_mng_ext const & ext = get_extension(env);
    if (ext.m_namespace_set.contains(n))
        return optional<name>(n);
    for (auto const & ns : ext.m_namespaces) {
        name r = ns + n;
        if (ext.m_namespace_set.contains(r))
            return optional<name>(r);
    }
    return optional<name>();
}

static std::string * g_new_namespace_key = nullptr;

environment add_namespace(environment const & env, name const & ns) {
    scope_mng_ext ext = get_extension(env);
    if (!ext.m_namespace_set.contains(ns)) {
        ext.m_namespace_set.insert(ns);
        environment r = update(env, ext);
        return module::add(r, *g_new_namespace_key, [=](environment const &, serializer & s) { s << ns; });
    } else {
        return env;
    }
}

environment push_scope(environment const & env, io_state const & ios, scope_kind k, name const & n) {
    if (k == scope_kind::Namespace && in_section(env))
        throw exception("invalid namespace declaration, a namespace cannot be declared inside a section");
    name new_n = get_namespace(env);
    if (k == scope_kind::Namespace)
        new_n = new_n + n;
    scope_mng_ext ext = get_extension(env);
    bool save_ns = false;
    if (!ext.m_namespace_set.contains(new_n)) {
        save_ns  = true;
        ext.m_namespace_set.insert(new_n);
    }
    ext.m_namespaces  = cons(new_n, ext.m_namespaces);
    ext.m_headers     = cons(n, ext.m_headers);
    ext.m_scope_kinds = cons(k, ext.m_scope_kinds);
    environment r = update(env, ext);
    for (auto const & t : get_exts()) {
        r = std::get<3>(t)(r, ios, k);
    }
    if (k == scope_kind::Namespace)
        r = using_namespace(r, ios, new_n);
    if (save_ns)
        r = module::add(r, *g_new_namespace_key, [=](environment const &, serializer & s) { s << new_n; });
    return r;
}

static void namespace_reader(deserializer & d, shared_environment &,
                             std::function<void(asynch_update_fn const &)> &,
                             std::function<void(delayed_update_fn const &)> & add_delayed_update) {
    name n;
    d >> n;
    add_delayed_update([=](environment const & env, io_state const &) -> environment {
            scope_mng_ext ext = get_extension(env);
            ext.m_namespace_set.insert(n);
            return update(env, ext);
        });
}

environment pop_scope_core(environment const & env, io_state const & ios) {
    scope_mng_ext ext = get_extension(env);
    if (is_nil(ext.m_namespaces))
        return env;
    scope_kind k      = head(ext.m_scope_kinds);
    ext.m_namespaces  = tail(ext.m_namespaces);
    ext.m_headers     = tail(ext.m_headers);
    ext.m_scope_kinds = tail(ext.m_scope_kinds);
    environment r = update(env, ext);
    for (auto const & t : get_exts()) {
        r = std::get<4>(t)(r, ios, k);
    }
    return r;
}

environment pop_scope(environment const & env, io_state const & ios, name const & n) {
    scope_mng_ext ext = get_extension(env);
    if (is_nil(ext.m_namespaces))
        throw exception("invalid end of scope, there are no open namespaces/sections");
    if (n != head(ext.m_headers))
        throw exception(sstream() << "invalid end of scope, begin/end mistmatch, scope starts with '"
                        << head(ext.m_headers) << "', and ends with '" << n << "'");
    return pop_scope_core(env, ios);
}

bool has_open_scopes(environment const & env) {
    scope_mng_ext ext = get_extension(env);
    return !is_nil(ext.m_namespaces);
}

static int using_namespace_objects(lua_State * L) {
    int nargs = lua_gettop(L);
    environment const & env = to_environment(L, 1);
    name n = to_name_ext(L, 2);
    if (nargs == 2)
        return push_environment(L, using_namespace(env, get_io_state(L), n));
    else if (nargs == 3)
        return push_environment(L, using_namespace(env, get_io_state(L), n, to_name_ext(L, 3)));
    else
        return push_environment(L, using_namespace(env, to_io_state(L, 4), n, to_name_ext(L, 3)));
}

static int push_scope(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1)
        return push_environment(L, push_scope(to_environment(L, 1), get_io_state(L), scope_kind::Section));
    else if (nargs == 2)
        return push_environment(L, push_scope(to_environment(L, 1), get_io_state(L), scope_kind::Namespace, to_name_ext(L, 2)));
    scope_kind k = static_cast<scope_kind>(lua_tonumber(L, 3));
    if (nargs == 3)
        return push_environment(L, push_scope(to_environment(L, 1), get_io_state(L), k, to_name_ext(L, 2)));
    else
        return push_environment(L, push_scope(to_environment(L, 1), to_io_state(L, 4), k, to_name_ext(L, 2)));
}

static int pop_scope(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1)
        return push_environment(L, pop_scope(to_environment(L, 1), get_io_state(L)));
    else
        return push_environment(L, pop_scope(to_environment(L, 1), get_io_state(L), to_name_ext(L, 2)));
}

void open_scoped_ext(lua_State * L) {
    SET_GLOBAL_FUN(using_namespace_objects, "using_namespace_objects");
    SET_GLOBAL_FUN(push_scope, "push_scope");
    SET_GLOBAL_FUN(pop_scope, "pop_scope");

    lua_newtable(L);
    SET_ENUM("Namespace",   scope_kind::Namespace);
    SET_ENUM("Section",     scope_kind::Section);
    lua_setglobal(L, "scope_kind");
}

void initialize_scoped_ext() {
    g_exts = new scoped_exts();
    g_ext  = new scope_mng_ext_reg();
    g_new_namespace_key = new std::string("nspace");
    register_module_object_reader(*g_new_namespace_key, namespace_reader);
}

void finalize_scoped_ext() {
    delete g_new_namespace_key;
    delete g_exts;
    delete g_ext;
}
}
