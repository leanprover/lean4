/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/aux_recursors.h"
#include "library/scoped_ext.h"
#include "library/module.h"

namespace lean {
struct aux_recursor_ext : public environment_extension {
    name_set m_set;
};

struct aux_recursor_ext_reg {
    unsigned m_ext_id;
    aux_recursor_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<aux_recursor_ext>()); }
};

static aux_recursor_ext_reg * g_ext = nullptr;
static aux_recursor_ext const & get_extension(environment const & env) {
    return static_cast<aux_recursor_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, aux_recursor_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<aux_recursor_ext>(ext));
}

static std::string * g_prv_key = nullptr;

environment add_aux_recursor(environment const & env, name const & r) {
    aux_recursor_ext ext = get_extension(env);
    ext.m_set.insert(r);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_prv_key, [=](environment const &, serializer & s) { s << r; });
}

bool is_aux_recursor(environment const & env, name const & r) {
    return get_extension(env).m_set.contains(r);
}

static void aux_recursor_reader(deserializer & d, shared_environment & senv,
                                std::function<void(asynch_update_fn const &)> &,
                                std::function<void(delayed_update_fn const &)> &) {
    name r;
    d >> r;
    senv.update([=](environment const & env) -> environment {
            aux_recursor_ext ext = get_extension(env);
            ext.m_set.insert(r);
            return update(env, ext);
        });
}

void initialize_aux_recursors() {
    g_ext     = new aux_recursor_ext_reg();
    g_prv_key = new std::string("auxrec");
    register_module_object_reader(*g_prv_key, aux_recursor_reader);
}

void finalize_aux_recursors() {
    delete g_prv_key;
    delete g_ext;
}
}
