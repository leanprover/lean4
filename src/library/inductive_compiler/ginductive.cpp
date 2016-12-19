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
    ginductive_kind m_kind;
    unsigned   m_num_params;
    list<name> m_inds;
    list<list<name> > m_intro_rules;
};

inline serializer & operator<<(serializer & s, ginductive_kind k) {
    switch (k) {
    case ginductive_kind::BASIC: s.write_unsigned(0); break;
    case ginductive_kind::MUTUAL: s.write_unsigned(1); break;
    case ginductive_kind::NESTED: s.write_unsigned(2); break;
    }
    return s;
}

inline deserializer & operator>>(deserializer & d, ginductive_kind & k) {
    unsigned i = d.read_unsigned();
    lean_assert(i <= 2);
    if (i == 0) k = ginductive_kind::BASIC;
    else if (i == 1) k = ginductive_kind::MUTUAL;
    else k = ginductive_kind::NESTED;
    return d;
}

serializer & operator<<(serializer & s, ginductive_entry const & entry);
ginductive_decl read_ginductive_decl(deserializer & d);
inline deserializer & operator>>(deserializer & d, ginductive_entry & entry);

serializer & operator<<(serializer & s, ginductive_entry const & entry) {
    s << entry.m_kind;
    s << entry.m_num_params;
    write_list<name>(s, entry.m_inds);
    for (list<name> const & irs : reverse(entry.m_intro_rules))
        write_list<name>(s, irs);
    return s;
}

ginductive_entry read_ginductive_entry(deserializer & d) {
    ginductive_entry entry;
    d >> entry.m_kind;
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

struct ginductive_env_ext : public environment_extension {
    list<name>                m_all_nested_inds;
    list<name>                m_all_mutual_inds;
    name_map<list<name> >     m_ind_to_irs;
    name_map<list<name> >     m_ind_to_mut_inds;
    name_map<ginductive_kind> m_ind_to_kind;
    name_map<unsigned>        m_num_params;
    name_map<name>            m_ir_to_ind;

    ginductive_env_ext() {}

    void register_ginductive_entry(ginductive_entry const & entry) {
        buffer<list<name> > intro_rules;
        to_buffer(entry.m_intro_rules, intro_rules);

        unsigned ind_idx = 0;
        for (name const & ind : entry.m_inds) {
            switch (entry.m_kind) {
            case ginductive_kind::BASIC: break;
            case ginductive_kind::MUTUAL: m_all_mutual_inds = list<name>(ind, m_all_mutual_inds); break;
            case ginductive_kind::NESTED: m_all_nested_inds = list<name>(ind, m_all_nested_inds); break;
            }
            m_ind_to_irs.insert(ind, intro_rules[ind_idx]);
            m_ind_to_mut_inds.insert(ind, entry.m_inds);
            m_ind_to_kind.insert(ind, entry.m_kind);
            m_num_params.insert(ind, entry.m_num_params);
            for (name const & ir : intro_rules[ind_idx]) {
                m_ir_to_ind.insert(ir, ind);
            }
        }
    }

    optional<ginductive_kind> is_ginductive(name const & ind_name) const {
        ginductive_kind const * k = m_ind_to_kind.find(ind_name);
        if (k)
            return optional<ginductive_kind>(*k);
        else
            return optional<ginductive_kind>();
    }

    list<name> get_intro_rules(name const & ind_name) const {
        list<name> const * ir_names = m_ind_to_irs.find(ind_name);
        lean_assert(ir_names);
        return *ir_names;
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

    list<name> get_all_nested_inds() const {
        return m_all_nested_inds;
    }

    list<name> get_all_mutual_inds() const {
        return m_all_mutual_inds;
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

struct ginductive_modification : public modification {
    LEAN_MODIFICATION("gind")

    ginductive_entry m_entry;

    ginductive_modification() {}
    ginductive_modification(ginductive_entry const & entry) : m_entry(entry) {}

    void perform(environment & env) const override {
        auto ext = get_extension(env);
        ext.register_ginductive_entry(m_entry);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_entry;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        ginductive_entry entry;
        d >> entry;
        return std::make_shared<ginductive_modification>(entry);
    }
};

environment register_ginductive_decl(environment const & env, ginductive_decl const & decl, ginductive_kind k) {
    ginductive_entry entry;
    entry.m_kind = k;
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

    return module::add_and_perform(env, std::make_shared<ginductive_modification>(entry));
}

optional<ginductive_kind> is_ginductive(environment const & env, name const & ind_name) {
    return get_extension(env).is_ginductive(ind_name);
}

list<name> get_ginductive_intro_rules(environment const & env, name const & ind_name) {
    return get_extension(env).get_intro_rules(ind_name);
}

optional<name> is_ginductive_intro_rule(environment const & env, name const & ir_name) {
    return get_extension(env).is_intro_rule(ir_name);
}

unsigned get_ginductive_num_params(environment const & env, name const & ind_name) {
    return get_extension(env).get_num_params(ind_name);
}

list<name> get_ginductive_mut_ind_names(environment const & env, name const & ind_name) {
    return get_extension(env).get_mut_ind_names(ind_name);
}

list<name> get_ginductive_all_mutual_inds(environment const & env) {
    return get_extension(env).get_all_mutual_inds();
}

list<name> get_ginductive_all_nested_inds(environment const & env) {
    return get_extension(env).get_all_nested_inds();
}

void initialize_inductive_compiler_ginductive() {
    ginductive_modification::init();
    g_ext                  = new ginductive_env_ext_reg();
}

void finalize_inductive_compiler_ginductive() {
    ginductive_modification::finalize();
    delete g_ext;
}
}
