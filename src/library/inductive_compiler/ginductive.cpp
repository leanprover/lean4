/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <utility>
#include <string>
#include "util/serializer.h"
#include "kernel/environment.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/module.h"
#include "library/kernel_serializer.h"

namespace lean {

struct ginductive_entry {
    unsigned   m_num_params;
    list<name> m_inds;
    list<list<name> > m_intro_rules;
};

serializer & operator<<(serializer & s, ginductive_entry const & entry);
ginductive_decl read_ginductive_decl(deserializer & d);
inline deserializer & operator>>(deserializer & d, ginductive_entry & entry);

serializer & operator<<(serializer & s, ginductive_entry const & entry) {
    s << entry.m_num_params;
    write_list<name>(s, entry.m_inds);
    for (list<name> const & irs : reverse(entry.m_intro_rules))
        write_list<name>(s, irs);
    return s;
}

ginductive_entry read_ginductive_entry(deserializer & d) {
    ginductive_entry entry;
    d >> entry.m_num_params;
    entry.m_inds    = read_list<name>(d, read_name);

    unsigned num_inds = length(entry.m_inds);
    for (unsigned i = 0; i < num_inds; ++i) {
        entry.m_intro_rules = list<list<name> >(read_list<name>(d, read_name), entry.m_intro_rules);
    }
    return entry;
}

inline deserializer & operator>>(deserializer & d, ginductive_entry & entry) {
    entry = read_ginductive_entry(d);
    return d;
}

static name * g_ginductive_extension = nullptr;
static std::string * g_ginductive_key = nullptr;

struct ginductive_env_ext : public environment_extension {
    name_map<list<name> > m_ind_to_irs;
    name_map<list<name> > m_ind_to_mut_inds;
    name_map<name>        m_ir_to_ind;
    name_map<unsigned>    m_num_params;

    ginductive_env_ext() {}

    void register_ginductive_entry(ginductive_entry const & entry) {
        buffer<list<name> > intro_rules;
        to_buffer(entry.m_intro_rules, intro_rules);

        unsigned ind_idx = 0;
        for (name const & ind : entry.m_inds) {
            m_num_params.insert(ind, entry.m_num_params);
            m_ind_to_irs.insert(ind, intro_rules[ind_idx]);
            m_ind_to_mut_inds.insert(ind, entry.m_inds);
            for (name const & ir : intro_rules[ind_idx]) {
                m_ir_to_ind.insert(ir, ind);
            }
        }
    }

    bool is_ginductive(name const & ind_name) const {
        return m_ind_to_irs.contains(ind_name);
    }

    optional<list<name> > get_intro_rules(name const & ind_name) const {
        list<name> const * ir_names = m_ind_to_irs.find(ind_name);
        if (ir_names)
            return optional<list<name> >(*ir_names);
        else
            return optional<list<name> >();
    }

    optional<name> is_intro_rule(name const & ir_name) const {
        name const * ind_name = m_ir_to_ind.find(ir_name);
        if (ind_name)
            return optional<name>(*ind_name);
        else
            return optional<name>();
    }

    unsigned get_num_params(name const & ind_name) const {
        unsigned const * num_params = m_num_params.find(ind_name);
        lean_assert(num_params);
        return *num_params;
    }

    list<name> get_mut_ind_names(name const & ind_name) const {
        list<name> const * mut_ind_names = m_ind_to_mut_inds.find(ind_name);
        lean_assert(mut_ind_names);
        return *mut_ind_names;
    }
};

struct ginductive_env_ext_reg {
    unsigned m_ext_id;
    ginductive_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<ginductive_env_ext>()); }
};

static ginductive_env_ext_reg * g_ext = nullptr;

static ginductive_env_ext const & get_extension(environment const & env) {
    return static_cast<ginductive_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

static environment update(environment const & env, ginductive_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<ginductive_env_ext>(ext));
}

environment register_ginductive_decl(environment const & env, ginductive_decl const & decl) {
    ginductive_env_ext ext(get_extension(env));

    ginductive_entry entry;
    entry.m_num_params = decl.get_num_params();

    buffer<name> inds;
    for (expr const & ind : decl.get_inds()) {
        inds.push_back(mlocal_name(ind));
    }
    entry.m_inds = to_list(inds);

    buffer<list<name> > intro_rules;
    for (buffer<expr> const & irs : decl.get_intro_rules()) {
        buffer<name> ir_names;
        for (expr const & ir : irs)
            ir_names.push_back(mlocal_name(ir));
        intro_rules.push_back(to_list(ir_names));
    }
    entry.m_intro_rules = to_list(intro_rules);

    ext.register_ginductive_entry(entry);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_ginductive_key, [=](environment const &, serializer & s) { s << entry; });
}

bool is_ginductive(environment const & env, name const & ind_name) {
    return get_extension(env).is_ginductive(ind_name);
}

optional<list<name> > get_ginductive_intro_rules(environment const & env, name const & ind_name) {
    return get_extension(env).get_intro_rules(ind_name);
}

optional<name> is_ginductive_intro_rule(environment const & env, name const & ir_name) {
    return get_extension(env).is_intro_rule(ir_name);
}

unsigned get_ginductive_num_params(environment const & env, name const & ind_name) {
    return get_extension(env).get_num_params(ind_name);
}

list<name> get_mut_ind_names(environment const & env, name const & ind_name) {
    return get_extension(env).get_mut_ind_names(ind_name);
}

static void ginductive_reader(deserializer & d, shared_environment & senv,
                              std::function<void(asynch_update_fn const &)> &,
                              std::function<void(delayed_update_fn const &)> &) {
    ginductive_entry entry;
    d >> entry;
    senv.update([=](environment const & env) -> environment {
            ginductive_env_ext ext = get_extension(env);
            ext.register_ginductive_entry(entry);
            return update(env, ext);
        });
}

void initialize_inductive_compiler_ginductive() {
    g_ginductive_extension = new name("ginductive_extension");
    g_ginductive_key       = new std::string("gind");
    g_ext                  = new ginductive_env_ext_reg();

    register_module_object_reader(*g_ginductive_key, ginductive_reader);
}

void finalize_inductive_compiler_ginductive() {
    delete g_ginductive_extension;
    delete g_ginductive_key;
    delete g_ext;
}
}
