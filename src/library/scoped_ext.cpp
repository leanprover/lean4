/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include <string>
#include "runtime/sstream.h"
#include "util/io.h"
#include "library/scoped_ext.h"

namespace lean {
typedef std::tuple<push_scope_fn, pop_scope_fn> entry;
typedef std::vector<entry> scoped_exts;
static scoped_exts * g_exts = nullptr;
static scoped_exts & get_exts() { return *g_exts; }

void register_scoped_ext(push_scope_fn push, pop_scope_fn pop) {
    get_exts().emplace_back(push, pop);
}

extern "C" object* lean_get_namespace(object* env);
extern "C" object* lean_get_namespaces(object* env);
extern "C" object* lean_get_scope_header(object* env);
extern "C" uint8 lean_in_section(object* env);
extern "C" uint8 lean_is_namespace(object* env, object * n);
extern "C" uint8 lean_has_open_scopes(object* env);
extern "C" uint8 lean_in_section(object* env);
extern "C" object* lean_get_scope_header(object* env);
extern "C" object* lean_to_valid_namespace(object* env, object * n);
extern "C" object* lean_register_namespace(object* env, object * n);
extern "C" object* lean_push_scope(object* env, object* header, uint8 isNamespace, object* w);
extern "C" object* lean_pop_scope(object* env, object* w);

name get_scope_header(environment const & env) { return name(lean_get_scope_header(env.to_obj_arg())); }
name get_namespace(environment const & env) { return name(lean_get_namespace(env.to_obj_arg())); }
names get_namespaces(environment const & env) { return names(lean_get_namespaces(env.to_obj_arg())); }
bool in_section(environment const & env) { return lean_in_section(env.to_obj_arg()); }
bool is_namespace(environment const & env, name const & n) { return lean_is_namespace(env.to_obj_arg(), n.to_obj_arg()); }
optional<name> to_valid_namespace_name(environment const & env, name const & n) {
    return to_optional<name>(lean_to_valid_namespace(env.to_obj_arg(), n.to_obj_arg()));
}
environment add_namespace(environment const & env, name const & n) { return environment(lean_register_namespace(env.to_obj_arg(), n.to_obj_arg())); }
bool has_open_scopes(environment const & env) { return lean_has_open_scopes(env.to_obj_arg()); }
environment push_scope(environment const & env, io_state const & ios, scope_kind k, name const & n) {
    environment r = get_io_result<environment>(lean_push_scope(env.to_obj_arg(), n.to_obj_arg(), k == scope_kind::Namespace, io_mk_world()));
    for (auto const & t : get_exts()) {
        r = std::get<0>(t)(r, ios, k);
    }
    return r;
}
environment pop_scope_core(environment const & env, io_state const & ios) {
    scope_kind k = lean_in_section(env.to_obj_arg()) ? scope_kind::Section : scope_kind::Namespace;
    environment r = get_io_result<environment>(lean_pop_scope(env.to_obj_arg(), io_mk_world()));
    for (auto const & t : get_exts()) {
        r = std::get<1>(t)(r, ios, k);
    }
    return r;
}
environment pop_scope(environment const & env, io_state const & ios, name const & n) {
    // TODO(Leo) this kind of check should be performed in the new frontend
    if (!has_open_scopes(env))
        throw exception("invalid end of scope, there are no open namespaces/sections");
    if (n != get_scope_header(env))
        throw exception("invalid end of scope, begin/end mismatch");
    return pop_scope_core(env, ios);
}

// temporary HACK
environment set_namespace(environment const & env, name const & /* ns */) {
    return env;
}

void initialize_scoped_ext() {
    g_exts = new scoped_exts();
}

void finalize_scoped_ext() {
    delete g_exts;
}
}
