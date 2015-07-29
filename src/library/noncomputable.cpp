/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/util.h"
#include "library/fingerprint.h"

namespace lean {
struct noncomputable_ext : public environment_extension {
    name_set m_noncomputable;
    noncomputable_ext() {}
};

struct noncomputable_ext_reg {
    unsigned m_ext_id;
    noncomputable_ext_reg() {
        m_ext_id = environment::register_extension(std::make_shared<noncomputable_ext>());
    }
};

static noncomputable_ext_reg * g_ext = nullptr;
static noncomputable_ext const & get_extension(environment const & env) {
    return static_cast<noncomputable_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, noncomputable_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<noncomputable_ext>(ext));
}

static name * g_noncomputable = nullptr;
static std::string * g_key    = nullptr;

static void noncomputable_reader(deserializer & d, shared_environment & senv,
                                 std::function<void(asynch_update_fn const &)> &,
                                 std::function<void(delayed_update_fn const &)> &) {
    name n;
    d >> n;
    senv.update([=](environment const & env) -> environment {
            noncomputable_ext ext = get_extension(env);
            ext.m_noncomputable.insert(n);
            return update(env, ext);
        });
}

static bool is_noncomputable(type_checker & tc, noncomputable_ext const & ext, name const & n) {
    if (ext.m_noncomputable.contains(n))
        return true;
    declaration const & d = tc.env().get(n);
    return d.is_axiom() && !tc.is_prop(d.get_type()).first;
}

bool is_noncomputable(environment const & env, name const & n) {
    type_checker tc(env);
    auto ext = get_extension(env);
    return is_noncomputable(tc, ext, n);
}

bool is_marked_noncomputable(environment const & env, name const & n) {
    auto ext = get_extension(env);
    return ext.m_noncomputable.contains(n);
}

environment mark_noncomputable(environment const & env, name const & n) {
    auto ext = get_extension(env);
    ext.m_noncomputable.insert(n);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_key, [=](environment const &, serializer & s) { s << n; });
}

optional<name> get_noncomputable_reason(environment const & env, name const & n) {
    if (!is_standard(env))
        return optional<name>(); // do nothing if it is not a standard kernel
    declaration const & d = env.get(n);
    if (!d.is_definition())
        return optional<name>();
    type_checker tc(env);
    if (tc.is_prop(d.get_type()).first)
        return optional<name>(); // definition is a proposition, then do nothing
    expr const & v = d.get_value();
    auto ext = get_extension(env);
    optional<name> r;
    for_each(v, [&](expr const & e, unsigned) {
            if (is_constant(e) && is_noncomputable(tc, ext, const_name(e))) {
                r = const_name(e);
            }
            return true;
        });
    return r;
}

bool check_computable(environment const & env, name const & n) {
    return !get_noncomputable_reason(env, n);
}

void initialize_noncomputable() {
    g_ext           = new noncomputable_ext_reg();
    g_noncomputable = new name("noncomputable");
    g_key           = new std::string("ncomp");
    register_module_object_reader(*g_key, noncomputable_reader);
}

void finalize_noncomputable() {
    delete g_key;
    delete g_noncomputable;
    delete g_ext;
}
}
