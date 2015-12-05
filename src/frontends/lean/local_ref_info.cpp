/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/scoped_ext.h"

namespace lean {
/*
When we declare a definition in a section, we create an alias for it that fixes the parameters in
universe parameters. We have to store the number of parameters and universes that have been fixed
to be able to correctly pretty print terms.
*/
struct local_ref_entry {
    name     m_name;
    expr     m_ref;
    local_ref_entry() {}
    local_ref_entry(name const & n, expr const & ref):
    m_name(n), m_ref(ref) {}
};

static name * g_local_ref_name  = nullptr;
static std::string * g_key      = nullptr;

struct local_ref_config {
    typedef name_map<expr>   state;
    typedef local_ref_entry  entry;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.insert(e.m_name, e.m_ref);
    }
    static name const & get_class_name() {
        return *g_local_ref_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer &, entry const &) {
        lean_unreachable();
    }
    static entry read_entry(deserializer &) {
        lean_unreachable();
    }
    static optional<unsigned> get_fingerprint(entry const &) {
        return optional<unsigned>();
    }
};

template class scoped_ext<local_ref_config>;
typedef scoped_ext<local_ref_config> local_ref_ext;

environment save_local_ref_info(environment const & env, name const & n, expr const & ref) {
    bool persistent = false;
    return local_ref_ext::add_entry(env, get_dummy_ios(), local_ref_entry(n, ref), get_namespace(env), persistent);
}

optional<expr> get_local_ref_info(environment const & env, name const & n) {
    if (auto r = local_ref_ext::get_state(env).find(n))
        return some_expr(*r);
    else
        return none_expr();
}

void initialize_local_ref_info() {
    g_local_ref_name = new name("localrefinfo");
    g_key            = new std::string("localrefinfo");
    local_ref_ext::initialize();
}

void finalize_local_ref_info() {
    local_ref_ext::finalize();
    delete g_local_ref_name;
    delete g_key;
}
}
