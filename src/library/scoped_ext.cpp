/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include <string>
#include "runtime/sstream.h"
#include "library/scoped_ext.h"

namespace lean {
typedef std::tuple<push_scope_fn, pop_scope_fn> entry;
typedef std::vector<entry> scoped_exts;
static scoped_exts * g_exts = nullptr;
static scoped_exts & get_exts() { return *g_exts; }

void register_scoped_ext(push_scope_fn push, pop_scope_fn pop) {
    get_exts().emplace_back(push, pop);
}

struct scope_mng_ext : public environment_extension {
    name_set         m_namespace_set;     // all namespaces registered in the system
    name_set         m_opened_namespaces; // set of namespaces marked as "open"
    names       m_namespaces;        // stack of namespaces/sections
    names       m_headers;           // namespace/section header
    list<scope_kind> m_scope_kinds;
};

struct scope_mng_ext_reg {
    unsigned m_ext_id;
    scope_mng_ext_reg() { m_ext_id = environment::register_extension(new scope_mng_ext()); }
};

static scope_mng_ext_reg * g_ext = nullptr;
static scope_mng_ext const & get_extension(environment const & env) {
    return static_cast<scope_mng_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, scope_mng_ext const & ext) {
    return env.update(g_ext->m_ext_id, new scope_mng_ext(ext));
}

name const & get_namespace(environment const & env) {
    scope_mng_ext const & ext = get_extension(env);
    return !is_nil(ext.m_namespaces) ? head(ext.m_namespaces) : name::anonymous();
}
// temporary HACK
environment set_namespace(environment const & env, name const & ns) {
    scope_mng_ext ext;
    ext.m_namespaces = {ns};
    return update(env, ext);
}

name const & get_scope_header(environment const & env) {
    scope_mng_ext const & ext = get_extension(env);
    return !is_nil(ext.m_namespaces) ? head(ext.m_headers) : name::anonymous();
}

names const & get_namespaces(environment const & env) {
    return get_extension(env).m_namespaces;
}

bool in_section(environment const & env) {
    scope_mng_ext const & ext = get_extension(env);
    return !is_nil(ext.m_scope_kinds) && head(ext.m_scope_kinds) == scope_kind::Section;
}

environment mark_namespace_as_open(environment const & env, name const & n) {
    scope_mng_ext ext = get_extension(env);
    ext.m_opened_namespaces.insert(n);
    return update(env, ext);
}

name_set get_opened_namespaces(environment const & env) {
    return get_extension(env).m_opened_namespaces;
}

bool is_namespace(environment const & env, name const & n) {
    return get_extension(env).m_namespace_set.contains(n);
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

std::vector<name> get_namespace_completion_candidates(environment const & env) {
    std::vector<name> ret;
    scope_mng_ext const & ext = get_extension(env);
    ext.m_namespace_set.for_each([&](name const & ns) {
        ret.push_back(ns);
        for (auto const & open_ns : ext.m_namespaces)
            if (open_ns != ns && is_prefix_of(open_ns, ns))
                ret.push_back(ns.replace_prefix(open_ns, {}));
    });
    return ret;
}

struct new_namespace_modification : public modification {
    LEAN_MODIFICATION("nspace")

    name m_ns;

    new_namespace_modification(name const & ns) : m_ns(ns) {}
    new_namespace_modification() {}

    void perform(environment & env) const override {
        scope_mng_ext ext = get_extension(env);
        ext.m_namespace_set.insert(m_ns);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_ns;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name n;
        d >> n;
        return std::make_shared<new_namespace_modification>(n);
    }
};

environment add_namespace(environment const & env, name const & ns) {
    scope_mng_ext ext = get_extension(env);
    if (!ext.m_namespace_set.contains(ns)) {
        ext.m_namespace_set.insert(ns);
        environment r = update(env, ext);
        r = module::add(r, std::make_shared<new_namespace_modification>(ns));
        if (ns.is_atomic())
            return r;
        else
            return add_namespace(r, ns.get_prefix());
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
        r = std::get<0>(t)(r, ios, k);
    }
    if (save_ns)
        r = module::add(r, std::make_shared<new_namespace_modification>(new_n));
    return r;
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
        r = std::get<1>(t)(r, ios, k);
    }
    return r;
}

environment pop_scope(environment const & env, io_state const & ios, name const & n) {
    scope_mng_ext ext = get_extension(env);
    if (is_nil(ext.m_namespaces))
        throw exception("invalid end of scope, there are no open namespaces/sections");
    if (n != head(ext.m_headers))
        throw exception(sstream() << "invalid end of scope, begin/end mismatch, scope starts with '"
                        << head(ext.m_headers) << "', and ends with '" << n << "'");
    return pop_scope_core(env, ios);
}

bool has_open_scopes(environment const & env) {
    scope_mng_ext ext = get_extension(env);
    return !is_nil(ext.m_namespaces);
}

void initialize_scoped_ext() {
    g_exts = new scoped_exts();
    g_ext  = new scope_mng_ext_reg();
    new_namespace_modification::init();
}

void finalize_scoped_ext() {
    new_namespace_modification::finalize();
    delete g_exts;
    delete g_ext;
}
}
