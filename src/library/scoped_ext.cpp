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

object* get_namespace_core(object* env);
object* get_namespaces_core(object* env);
object* get_scope_header_core(object* env);
uint8 in_section_core(object* env);
uint8 is_namespace_core(object* env, object * n);
uint8 has_open_scopes_core(object* env);
uint8 in_section_core(object* env);
object* get_scope_header_core(object* env);
object* to_valid_namespace_core(object* env, object * n);
object* register_namespace_core(object* env, object * n);
object* push_scope_core(object* env, object* header, uint8 isNamespace, object* w);
object* pop_scope_core(object* env, object* w);

name get_scope_header(environment const & env) { return name(get_scope_header_core(env.to_obj_arg())); }
name get_namespace(environment const & env) { return name(get_namespace_core(env.to_obj_arg())); }
names get_namespaces(environment const & env) { return names(get_namespaces_core(env.to_obj_arg())); }
bool in_section(environment const & env) { return in_section_core(env.to_obj_arg()); }
bool is_namespace(environment const & env, name const & n) { return is_namespace_core(env.to_obj_arg(), n.to_obj_arg()); }
optional<name> to_valid_namespace_name(environment const & env, name const & n) {
    return to_optional<name>(to_valid_namespace_core(env.to_obj_arg(), n.to_obj_arg()));
}
environment add_namespace(environment const & env, name const & n) { return environment(register_namespace_core(env.to_obj_arg(), n.to_obj_arg())); }
bool has_open_scopes(environment const & env) { return has_open_scopes_core(env.to_obj_arg()); }
environment push_scope(environment const & env, io_state const & ios, scope_kind k, name const & n) {
    environment r = get_io_result<environment>(push_scope_core(env.to_obj_arg(), n.to_obj_arg(), k == scope_kind::Namespace, io_mk_world()));
    for (auto const & t : get_exts()) {
        r = std::get<0>(t)(r, ios, k);
    }
    return r;
}
environment pop_scope_core(environment const & env, io_state const & ios) {
    scope_kind k = in_section_core(env.to_obj_arg()) ? scope_kind::Section : scope_kind::Namespace;
    environment r = get_io_result<environment>(pop_scope_core(env.to_obj_arg(), io_mk_world()));
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
