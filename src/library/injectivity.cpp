/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/type_checker.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/attribute_manager.h"
#include "library/injectivity.h"

namespace lean {
struct injectivity_entry {
    name             m_fn;
    injectivity_info m_info;
    injectivity_entry() {}
    injectivity_entry(name const & fn, injectivity_info const & info):
        m_fn(fn), m_info(info) {}
};

struct injectivity_state {
    name_map<injectivity_info> m_fn_info;  /* mapping from function to its inverse and lemma */
    name_map<name>             m_inv_info; /* mapping from inverse to function */

    void add(injectivity_entry const & e) {
        m_fn_info.insert(e.m_fn, e.m_info);
        m_inv_info.insert(e.m_info.m_inv, e.m_fn);
    }
};

static name * g_injectivity_name = nullptr;
static std::string * g_key = nullptr;

struct injectivity_config {
    typedef injectivity_state state;
    typedef injectivity_entry entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.add(e);
    }
    static name const & get_class_name() {
        return *g_injectivity_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_fn << e.m_info.m_arity << e.m_info.m_inv << e.m_info.m_lemma;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_fn >> e.m_info.m_arity >> e.m_info.m_inv >> e.m_info.m_lemma;
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.m_info.m_lemma.hash());
    }
};

template class scoped_ext<injectivity_config>;
typedef scoped_ext<injectivity_config> injectivity_ext;

optional<injectivity_info> has_inverse(environment const & env, name const & fn) {
    if (auto r = injectivity_ext::get_state(env).m_fn_info.find(fn))
        return optional<injectivity_info>(*r);
    else
        return optional<injectivity_info>();
}

optional<name> is_inverse(environment const & env, name const & inv) {
    if (auto r = injectivity_ext::get_state(env).m_inv_info.find(inv))
        return optional<name>(*r);
    else
        return optional<name>();
}

void throw_injectivity_error() {
    throw exception("invalid injectivity lemma, "
                    "it should be of the form: (f ... (g ... x)) = x");
}

environment add_injectivity_lemma(environment const & env, name const & lemma, bool persistent) {
    type_checker tc(env);
    declaration d = env.get(lemma);
    buffer<expr> tele;
    expr type     = to_telescope(tc, d.get_type(), tele);
    expr lhs, rhs;
    if (!is_eq(type, lhs, rhs) || !is_app(lhs) || !is_constant(get_app_fn(lhs)) || !is_local(rhs))
        throw_injectivity_error();
    injectivity_info info;
    buffer<expr> lhs_args;
    expr const & lhs_fn = get_app_args(lhs, lhs_args);
    info.m_inv   = const_name(lhs_fn);
    info.m_lemma = lemma;
    expr const & last_arg = lhs_args.back();
    if (!is_app(last_arg) || !is_constant(get_app_fn(last_arg)))
        throw_injectivity_error();
    buffer<expr> last_arg_args;
    expr const & fn = get_app_args(last_arg, last_arg_args);
    if (last_arg_args.back() != rhs)
        throw_injectivity_error();
    info.m_arity = last_arg_args.size();
    return injectivity_ext::add_entry(env, get_dummy_ios(), injectivity_entry(const_name(fn), info), persistent);
}

void initialize_injectivity() {
    g_injectivity_name = new name("injectivity");
    g_key = new std::string("injectivity");
    injectivity_ext::initialize();

    register_system_attribute(basic_attribute("injectivity", "attribute for marking injectivity lemmas "
                                              "used by the equation compiler",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_injectivity_lemma(env, d, persistent);
                                              }));
}

void finalize_injectivity() {
    injectivity_ext::finalize();
    delete g_key;
    delete g_injectivity_name;
}
}
