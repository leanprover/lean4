/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/serializer.h"
#include "library/export_decl.h"
#include "library/scoped_ext.h"

namespace lean {

static void write_pair_name(serializer & s, pair<name, name> const & p) {
    s << p.first << p.second;
}

static serializer & operator<<(serializer & s, pair<name, name> const & p) {
    write_pair_name(s, p);
    return s;
}

static pair<name, name> read_pair_name(deserializer & d) {
    pair<name, name> r;
    d >> r.first >> r.second;
    return r;
}

bool operator==(export_decl const & d1, export_decl const & d2) {
    return
        d1.m_ns           == d2.m_ns &&
        d1.m_as           == d2.m_as &&
        d1.m_had_explicit == d2.m_had_explicit &&
        d1.m_renames      == d2.m_renames &&
        d1.m_except_names == d2.m_except_names;
}

bool operator!=(export_decl const & d1, export_decl const & d2) {
    return !(d1 == d2);
}

struct export_decl_env_ext : public environment_extension {
    name_map<list<export_decl>> m_ns_map;

    export_decl_env_ext() {}
    export_decl_env_ext(name_map<list<export_decl>> const & ns_map): m_ns_map(ns_map) {}
};

/** \brief Auxiliary object for registering the environment extension */
struct export_decl_env_ext_reg {
    unsigned m_ext_id;
    export_decl_env_ext_reg() { m_ext_id = environment::register_extension(new export_decl_env_ext()); }
};

static export_decl_env_ext_reg * g_ext = nullptr;

/** \brief Retrieve environment extension */
static export_decl_env_ext const & get_export_decl_extension(environment const & env) {
    return static_cast<export_decl_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

/** \brief Update environment extension */
static environment update(environment const & env, export_decl_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, new export_decl_env_ext(ext));
}

static environment add_export_decl_core(environment const & env, name const & in_ns, export_decl const & e) {
    auto ns_map = get_export_decl_extension(env).m_ns_map;
    list<export_decl> decls;
    if (ns_map.contains(in_ns))
        decls = *ns_map.find(in_ns);

    if (std::find(decls.begin(), decls.end(), e) != decls.end())
        return env;

    return update(env, export_decl_env_ext(insert(ns_map, in_ns, cons(e, decls))));
}

struct export_decl_modification : public modification {
    LEAN_MODIFICATION("export_decl")

    name m_in_ns;
    export_decl m_export_decl;

    export_decl_modification() {}
    export_decl_modification(name const & in_ns, export_decl const & e) :
        m_in_ns(in_ns), m_export_decl(e) {}

    void perform(environment & env) const override {
        env = add_export_decl_core(env, m_in_ns, m_export_decl);
    }

    void serialize(serializer & s) const override {
        s << m_in_ns << m_export_decl.m_ns << m_export_decl.m_as << m_export_decl.m_had_explicit;
        s << m_export_decl.m_except_names;
        write_list<pair<name, name>>(s, m_export_decl.m_renames);
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        auto m = std::make_shared<export_decl_modification>();
        auto & e = m->m_export_decl;
        d >> m->m_in_ns >> e.m_ns >> e.m_as >> e.m_had_explicit;
        e.m_except_names = read_names(d);
        e.m_renames = read_list<pair<name, name>>(d, read_pair_name);
        return m;
    }
};

environment add_export_decl(environment const & env, name const & in_ns, export_decl const & e) {
    environment new_env = add_export_decl_core(env, in_ns, e);
    return module::add(new_env, std::make_shared<export_decl_modification>(in_ns, e));
}

environment add_export_decl(environment const & env, export_decl const & entry) {
    return add_export_decl(env, get_namespace(env), entry);
}

struct active_export_decls_config {
    typedef export_decl       entry;
    typedef list<export_decl> state;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        if (std::find(s.begin(), s.end(), e) == s.end()) {
            s = cons(e, s);
        }
    }
    static optional<unsigned> get_fingerprint(entry const &) {
        return optional<unsigned>();
    }

    // uses local scope only
    static const char * get_serialization_key() { return "active_export_decls"; }
    static void write_entry(serializer &, entry const &) { lean_unreachable(); }
    static entry read_entry(deserializer &) { lean_unreachable(); }
};

template class scoped_ext<active_export_decls_config>;
typedef scoped_ext<active_export_decls_config> active_export_decls_ext;

environment activate_export_decls(environment env, name ns) {
    auto ns_map = get_export_decl_extension(env).m_ns_map;
    while (true) {
        if (ns_map.contains(ns)) {
            for (auto const & e : *ns_map.find(ns))
                env = active_export_decls_ext::add_entry(env, get_dummy_ios(), e, false);
        }
        if (ns.is_anonymous())
            break;
        ns = ns.get_prefix();
    }
    return env;
}

list<export_decl> get_active_export_decls(environment const & env) {
    return active_export_decls_ext::get_state(env);
}

void initialize_export_decl() {
    g_ext = new export_decl_env_ext_reg();
    export_decl_modification::init();
    active_export_decls_ext::initialize();
}

void finalize_export_decl() {
    active_export_decls_ext::finalize();
    export_decl_modification::finalize();
    delete g_ext;
}
}
