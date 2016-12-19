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
#include "library/library_system.h"

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

struct noncomputable_modification : public modification {
    LEAN_MODIFICATION("ncomp")

    name m_decl;

    noncomputable_modification() {}
    noncomputable_modification(name const & decl) : m_decl(decl) {}

    void perform(environment & env) const override {
        noncomputable_ext ext = get_extension(env);
        ext.m_noncomputable.insert(m_decl);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<noncomputable_modification>(read_name(d));
    }
};

static bool is_noncomputable(type_checker & tc, noncomputable_ext const & ext, name const & n) {
    environment const & env = tc.env();
    if (ext.m_noncomputable.contains(n))
        return true;
    declaration const & d = env.get(n);
    if (!d.is_trusted()) {
        return false; /* ignore nontrusted definitions */
    } else if (d.is_axiom() && !tc.is_prop(d.get_type())) {
        return true;
    } else if (d.is_constant_assumption()) {
        return !env.is_builtin(d.get_name()) && !is_system_builtin(d.get_name()) && !tc.is_prop(d.get_type());
    } else {
        return false;
    }
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
    return module::add(new_env, std::make_shared<noncomputable_modification>(n));
}

optional<name> get_noncomputable_reason(environment const & env, name const & n) {
    declaration const & d = env.get(n);
    if (!d.is_definition())
        return optional<name>();
    type_checker tc(env);
    if (tc.is_prop(d.get_type()))
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
    noncomputable_modification::init();
}

void finalize_noncomputable() {
    noncomputable_modification::finalize();
    delete g_ext;
}
}
