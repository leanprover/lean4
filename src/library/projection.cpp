/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/inductive.h"
#include "library/util.h"
#include "library/projection.h"
#include "library/module.h"

namespace lean {
/** \brief This environment extension stores information about all projection functions
    defined in an environment object.
*/
struct projection_ext : public environment_extension {
    name_map<projection_info> m_info;
    projection_ext() {}
};

struct projection_ext_reg {
    unsigned m_ext_id;
    projection_ext_reg() {
        m_ext_id = environment::register_extension(new projection_ext());
    }
};

static projection_ext_reg * g_ext = nullptr;
static projection_ext const & get_extension(environment const & env) {
    return static_cast<projection_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, projection_ext const & ext) {
    return env.update(g_ext->m_ext_id, new projection_ext(ext));
}

struct proj_modification : public modification {
    LEAN_MODIFICATION("proj")

    name m_proj;
    projection_info m_info;

    proj_modification() {}
    proj_modification(name const & proj, projection_info const & info) : m_proj(proj), m_info(info) {}

    void perform(environment & env) const override {
        projection_ext ext = get_extension(env);
        ext.m_info.insert(m_proj, m_info);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_proj << m_info.m_constructor << m_info.m_nparams << m_info.m_i << m_info.m_inst_implicit;
    }

    static modification* deserialize(deserializer & d) {
        name p, mk; unsigned nparams, i; bool inst_implicit;
        d >> p >> mk >> nparams >> i >> inst_implicit;
        return new proj_modification(p, projection_info(mk, nparams, i, inst_implicit));
    }
};

environment save_projection_info(environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i, bool inst_implicit) {
    return module::add_and_perform(env, new proj_modification(p, projection_info(mk, nparams, i, inst_implicit)));
}

optional<projection_info> get_projection_info(environment const & env, name const & p) {
    projection_ext const & ext = get_extension(env);
    if (auto info = ext.m_info.find(p))
        return optional<projection_info>(*info);
    else
        return optional<projection_info>();
}

/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos.
*/
bool is_structure_like(environment const & env, name const & S) {
    constant_info S_info = env.get(S);
    if (!S_info.is_inductive()) return false;
    inductive_val S_val = S_info.to_inductive_val();
    return length(S_val.get_cnstrs()) == 1 && S_val.get_nindices() == 0;
}

void initialize_projection() {
    g_ext      = new projection_ext_reg();
    proj_modification::init();
}

void finalize_projection() {
    proj_modification::finalize();
    delete g_ext;
}
}
