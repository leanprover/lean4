/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/aux_recursors.h"
#include "library/constants.h"
#include "library/module.h"

namespace lean {
struct aux_recursor_ext : public environment_extension {
    name_set m_aux_recursor_set;
    name_set m_no_confusion_set;
};

struct aux_recursor_ext_reg {
    unsigned m_ext_id;
    aux_recursor_ext_reg() { m_ext_id = environment::register_extension(new aux_recursor_ext()); }
};

static aux_recursor_ext_reg * g_ext = nullptr;
static aux_recursor_ext const & get_extension(environment const & env) {
    return static_cast<aux_recursor_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, aux_recursor_ext const & ext) {
    return env.update(g_ext->m_ext_id, new aux_recursor_ext(ext));
}

struct auxrec_modification : public modification {
    LEAN_MODIFICATION("auxrec")

    name m_decl;

    auxrec_modification() {}
    auxrec_modification(name const & decl) : m_decl(decl) {}

    void perform(environment & env) const override {
        aux_recursor_ext ext = get_extension(env);
        ext.m_aux_recursor_set.insert(m_decl);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<auxrec_modification>(read_name(d));
    }
};

struct no_conf_modification : public modification {
    LEAN_MODIFICATION("no_conf")

    name m_decl;

    no_conf_modification() {}
    no_conf_modification(name const & decl) : m_decl(decl) {}

    void perform(environment & env) const override {
        aux_recursor_ext ext = get_extension(env);
        ext.m_no_confusion_set.insert(m_decl);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<no_conf_modification>(read_name(d));
    }
};

environment add_aux_recursor(environment const & env, name const & r) {
    return module::add_and_perform(env, std::make_shared<auxrec_modification>(r));
}

environment add_no_confusion(environment const & env, name const & r) {
    return module::add_and_perform(env, std::make_shared<no_conf_modification>(r));
}

bool is_aux_recursor(environment const & env, name const & r) {
    return get_extension(env).m_aux_recursor_set.contains(r);
}

bool is_no_confusion(environment const & env, name const & r) {
    return get_extension(env).m_no_confusion_set.contains(r);
}

void initialize_aux_recursors() {
    g_ext              = new aux_recursor_ext_reg();
    auxrec_modification::init();
    no_conf_modification::init();
}

void finalize_aux_recursors() {
    auxrec_modification::finalize();
    no_conf_modification::finalize();
    delete g_ext;
}
}
