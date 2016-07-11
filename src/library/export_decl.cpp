/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/serializer.h"
#include "library/export_decl.h"
#include "library/scoped_ext.h"

namespace lean {
static std::string * g_key = nullptr;

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

struct export_decl_config {
    typedef export_decl       entry;
    typedef list<export_decl> state;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        if (std::find(s.begin(), s.end(), e) == s.end()) {
            s = cons(e, s);
        }
    }

    static std::string const & get_serialization_key() {
        return *g_key;
    }

    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_ns << e.m_as << e.m_had_explicit;
        write_list<name>(s, e.m_except_names);
        write_list<pair<name, name>>(s, e.m_renames);
    }

    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_ns >> e.m_as >> e.m_had_explicit;
        e.m_except_names = read_list<name>(d, read_name);
        e.m_renames      = read_list<pair<name, name>>(d, read_pair_name);
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const &) {
        return optional<unsigned>();
    }
};

template class scoped_ext<export_decl_config>;
typedef scoped_ext<export_decl_config> export_decl_ext;

environment add_export_decl(environment const & env, export_decl const & entry) {
    bool persistent = true;
    return export_decl_ext::add_entry(env, get_dummy_ios(), entry, persistent);
}

list<export_decl> get_export_decls(environment const & env) {
    return export_decl_ext::get_state(env);
}

void initialize_export_decl() {
    g_key = new std::string("export_decl");
    export_decl_ext::initialize();
}

void finalize_export_decl() {
    delete g_key;
    export_decl_ext::finalize();
}
}
