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

namespace lean {
struct reducible_entry {
    reducible_status m_status;
    name             m_name;
    reducible_entry():m_status(reducible_status::None) {}
    reducible_entry(reducible_status s, name const & n):m_status(s), m_name(n) {}
};

struct reducible_state {
    name_set m_reducible_on;
    name_set m_reducible_off;

    void add(reducible_entry const & e) {
        switch (e.m_status) {
        case reducible_status::On:
            m_reducible_on.insert(e.m_name);
            m_reducible_off.erase(e.m_name);
            break;
        case reducible_status::Off:
            m_reducible_on.erase(e.m_name);
            m_reducible_off.insert(e.m_name);
            break;
        case reducible_status::None:
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
    g_class_name = new name("reduce_hints");
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

std::unique_ptr<type_checker> mk_type_checker(environment const & env, name_generator const & ngen,
                                              bool relax_main_opaque, reducible_behavior rb,
                                              bool memoize) {
    reducible_state const & s = reducible_ext::get_state(env);
    if (rb == OpaqueIfNotReducibleOn) {
        name_set reducible_on  = s.m_reducible_on;
        name_set reducible_off = s.m_reducible_off;
        extra_opaque_pred pred([=](name const & n) { return !reducible_on.contains(n); });
        return std::unique_ptr<type_checker>(new type_checker(env, ngen, mk_default_converter(env, relax_main_opaque,
                                                                                              memoize, pred)));
    } else {
        name_set reducible_off = s.m_reducible_off;
        extra_opaque_pred pred([=](name const & n) { return reducible_off.contains(n); });
        return std::unique_ptr<type_checker>(new type_checker(env, ngen, mk_default_converter(env, relax_main_opaque,
                                                                                              memoize, pred)));
    }
}

std::unique_ptr<type_checker> mk_type_checker(environment const & env, bool relax_main_opaque, reducible_behavior rb) {
    return mk_type_checker(env, name_generator(*g_tmp_prefix), relax_main_opaque, rb);
}

std::unique_ptr<type_checker> mk_opaque_type_checker(environment const & env, name_generator const & ngen) {
    extra_opaque_pred pred([=](name const &) { return true; }); // everything is opaque
    bool relax_main_opaque = false;
    bool memoize = true;
    return std::unique_ptr<type_checker>(new type_checker(env, ngen, mk_default_converter(env, relax_main_opaque,
                                                                                          memoize, pred)));
}
}
