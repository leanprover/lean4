/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/aux_recursors.h"
#include "library/constants.h"
#include "library/scoped_ext.h"
#include "library/module.h"

namespace lean {
struct aux_recursor_ext : public environment_extension {
    name_set m_aux_recursor_set;
    name_set m_no_confusion_set;
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

static std::string * g_auxrec_key = nullptr;
static std::string * g_no_confusion_key = nullptr;

environment add_aux_recursor(environment const & env, name const & r) {
    aux_recursor_ext ext = get_extension(env);
    ext.m_aux_recursor_set.insert(r);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_auxrec_key, [=](environment const &, serializer & s) { s << r; });
}

environment add_no_confusion(environment const & env, name const & r) {
    aux_recursor_ext ext = get_extension(env);
    ext.m_no_confusion_set.insert(r);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_no_confusion_key, [=](environment const &, serializer & s) { s << r; });
}

bool is_aux_recursor(environment const & env, name const & r) {
    return get_extension(env).m_aux_recursor_set.contains(r);
}

bool is_no_confusion(environment const & env, name const & r) {
    return get_extension(env).m_no_confusion_set.contains(r);
}

static void aux_recursor_reader(deserializer & d, environment & env) {
    name r;
    d >> r;
    aux_recursor_ext ext = get_extension(env);
    ext.m_aux_recursor_set.insert(r);
    env = update(env, ext);
}

static void no_confusion_reader(deserializer & d, environment & env) {
    name r;
    d >> r;
    aux_recursor_ext ext = get_extension(env);
    ext.m_no_confusion_set.insert(r);
    env = update(env, ext);
}

void initialize_aux_recursors() {
    g_ext              = new aux_recursor_ext_reg();
    g_auxrec_key       = new std::string("auxrec");
    g_no_confusion_key = new std::string("no_conf");
    register_module_object_reader(*g_auxrec_key, aux_recursor_reader);
    register_module_object_reader(*g_no_confusion_key, no_confusion_reader);
}

void finalize_aux_recursors() {
    delete g_auxrec_key;
    delete g_no_confusion_key;
    delete g_ext;
}
}
