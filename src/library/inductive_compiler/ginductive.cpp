/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <utility>
#include <string>
#include "util/serializer.h"
#include "util/list_fn.h"
#include "kernel/environment.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/module.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"

namespace lean {
optional<name> is_gintro_rule_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn)) return optional<name>();
    if (!is_ginductive_intro_rule(env, const_name(fn))) return optional<name>();
    return optional<name>(const_name(fn));
}

expr whnf_ginductive(type_context_old & ctx, expr const & e) {
    return ctx.whnf_head_pred(e, [&](expr const & e) {
            expr const & fn = get_app_fn(e);
            if (!is_constant(fn)) return true;
            return !is_ginductive(ctx.env(), const_name(fn));
        });
}

expr whnf_gintro_rule(type_context_old & ctx, expr const & e) {
    return ctx.whnf_head_pred(e, [&](expr const & e) {
            return !is_gintro_rule_app(ctx.env(), e);
        });
}

expr whnf_ginductive_gintro_rule(type_context_old & ctx, expr const & e) {
    return ctx.whnf_head_pred(e, [&](expr const & e) {
            expr const & fn = get_app_fn(e);
            if (!is_constant(fn)) return true;
            return
                !is_ginductive_intro_rule(ctx.env(), const_name(fn)) &&
                !is_ginductive(ctx.env(), const_name(fn));
        });
}

static unsigned compute_idx_number(expr const & e) {
    buffer<expr> args;
    unsigned idx = 0;
    expr it = e;
    while (true) {
        args.clear();
        expr fn = get_app_args(it, args);
        if (is_constant(fn) && const_name(fn) == get_psum_inl_name()) {
            return idx;
        } else if (is_constant(fn) && const_name(fn) == get_psum_inr_name()) {
            idx++;
            lean_assert(args.size() == 3);
            it = args[2];
        } else {
            return idx;
        }
    }
    lean_unreachable();
}

struct ginductive_entry {
    ginductive_kind m_kind;
    bool       m_is_inner;
    unsigned   m_num_params;
    list<unsigned> m_num_indices;
    list<name> m_inds;
    list<list<name> > m_intro_rules;
    list<unsigned> m_ir_offsets;
    list<pair<unsigned, unsigned> > m_idx_to_ir_range;
    list<name> m_packs;
    list<name> m_unpacks;
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
    s << entry.m_is_inner;
    s << entry.m_num_params;
    write_list<unsigned>(s, entry.m_num_indices);
    write_list<name>(s, entry.m_inds);
    for (list<name> const & irs : reverse(entry.m_intro_rules))
        write_list<name>(s, irs);

    write_list<unsigned>(s, entry.m_ir_offsets);
    write_list<pair<unsigned, unsigned> >(s, entry.m_idx_to_ir_range);

    write_list<name>(s, entry.m_packs);
    write_list<name>(s, entry.m_unpacks);

    return s;
}

ginductive_entry read_ginductive_entry(deserializer & d) {
    ginductive_entry entry;
    d >> entry.m_kind;
    d >> entry.m_is_inner;
    d >> entry.m_num_params;
    entry.m_num_indices = read_list<unsigned>(d);
    entry.m_inds    = read_list<name>(d, read_name);

    unsigned num_inds = length(entry.m_inds);
    for (unsigned i = 0; i < num_inds; ++i) {
        entry.m_intro_rules = list<list<name> >(read_list<name>(d, read_name), entry.m_intro_rules);
    }

    entry.m_ir_offsets = read_list<unsigned>(d);
    entry.m_idx_to_ir_range = read_list<pair<unsigned, unsigned> >(d);

    entry.m_packs = read_list<name>(d, read_name);
    entry.m_unpacks = read_list<name>(d, read_name);
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
    name_map<unsigned>        m_num_indices;
    name_map<name>            m_ir_to_ind;

    name_set                                   m_inner_inds;
    name_set                                   m_inner_irs;
    name_map<unsigned>                         m_ir_to_simulated_ir_offset;
    name_map<list<pair<unsigned, unsigned> > > m_ind_to_ir_ranges;

    name_set                                   m_packs;
    name_set                                   m_unpacks;

    ginductive_env_ext() {}

    void register_ginductive_entry(ginductive_entry const & entry) {
        buffer<unsigned> num_indices;
        to_buffer(entry.m_num_indices, num_indices);

        buffer<list<name> > intro_rules;
        to_buffer(entry.m_intro_rules, intro_rules);

        buffer<unsigned> ir_offsets;
        to_buffer(entry.m_ir_offsets, ir_offsets);

        unsigned ind_idx = 0;
        unsigned acc_ir_idx = 0;
        for (name const & ind : entry.m_inds) {
            switch (entry.m_kind) {
            case ginductive_kind::BASIC: break;
            case ginductive_kind::MUTUAL: m_all_mutual_inds = list<name>(ind, m_all_mutual_inds); break;
            case ginductive_kind::NESTED: m_all_nested_inds = list<name>(ind, m_all_nested_inds); break;
            }

            if (entry.m_is_inner) {
                m_inner_inds.insert(ind);
            }
            m_ind_to_irs.insert(ind, intro_rules[ind_idx]);
            m_ind_to_mut_inds.insert(ind, entry.m_inds);
            m_ind_to_kind.insert(ind, entry.m_kind);
            m_num_params.insert(ind, entry.m_num_params);
            m_num_indices.insert(ind, num_indices[ind_idx]);
            for (name const & ir : intro_rules[ind_idx]) {
                m_ir_to_ind.insert(ir, ind);
                m_ir_to_simulated_ir_offset.insert(ir, ir_offsets[acc_ir_idx]);
                acc_ir_idx++;
                if (entry.m_is_inner) {
                    m_inner_irs.insert(ir);
                }
            }

            m_ind_to_ir_ranges.insert(ind, entry.m_idx_to_ir_range);
            ind_idx++;
        }

        for (name const & pack : entry.m_packs)
            m_packs.insert(pack);

        for (name const & unpack : entry.m_unpacks)
            m_unpacks.insert(unpack);
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

    unsigned get_num_indices(name const & ind_name) const {
        unsigned const * num_indices = m_num_indices.find(ind_name);
        lean_assert(num_indices);
        return *num_indices;
    }

    list<name> get_mut_ind_names(name const & ind_name) const {
        list<name> const * mut_ind_names = m_ind_to_mut_inds.find(ind_name);
        lean_assert(mut_ind_names);
        return *mut_ind_names;
    }

    unsigned ir_to_simulated_ir_offset(name const & basic_ir_name) const {
        unsigned const * offset = m_ir_to_simulated_ir_offset.find(basic_ir_name);
        lean_assert(offset);
        return *offset;
    }

    bool is_inner_ind(name const & ind_name) const {
        return m_inner_inds.contains(ind_name);
    }

    bool is_inner_ir(name const & ir_name) const {
        return m_inner_irs.contains(ir_name);
    }

    bool is_pack(name const & n) const {
        return m_packs.contains(n);
    }

    bool is_unpack(name const & n) const {
        return m_unpacks.contains(n);
    }

    pair<unsigned, unsigned> ind_indices_to_ir_range(name const & basic_ind_name, buffer<expr> const & idxs) const {
        if (!m_inner_inds.contains(basic_ind_name))
            return mk_pair(0, length(get_intro_rules(basic_ind_name)));

        lean_assert(idxs.size() == 1);
        unsigned idx_number = compute_idx_number(idxs[0]);

        list<pair<unsigned, unsigned> > const * ranges = m_ind_to_ir_ranges.find(basic_ind_name);
        lean_assert(ranges);
        return get_ith(*ranges, idx_number);
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
    entry.m_is_inner = decl.is_inner();
    entry.m_num_params = decl.get_num_params();
    entry.m_num_indices = to_list(decl.get_num_indices());

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
    entry.m_packs = to_list(decl.get_packs());
    entry.m_unpacks = to_list(decl.get_unpacks());

    entry.m_ir_offsets = to_list(decl.get_ir_offsets());
    entry.m_idx_to_ir_range = to_list(decl.get_idx_to_ir_range());

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

unsigned get_ginductive_num_indices(environment const & env, name const & ind_name) {
    return get_extension(env).get_num_indices(ind_name);
}

list<name> get_ginductive_mut_ind_names(environment const & env, name const & ind_name) {
    return get_extension(env).get_mut_ind_names(ind_name);
}

unsigned ir_to_simulated_ir_offset(environment const & env, name basic_ir_name) {
    return get_extension(env).ir_to_simulated_ir_offset(basic_ir_name);
}

pair<unsigned, unsigned> ind_indices_to_ir_range(environment const & env, name const & basic_ind_name, buffer<expr> const & idxs) {
    return get_extension(env).ind_indices_to_ir_range(basic_ind_name, idxs);
}

bool is_ginductive_inner_ind(environment const & env, name const & ind_name) {
    return get_extension(env).is_inner_ind(ind_name);
}

bool is_ginductive_inner_ir(environment const & env, name const & ir_name) {
    return get_extension(env).is_inner_ir(ir_name);
}

bool is_ginductive_pack(environment const & env, name const & n) {
    return get_extension(env).is_pack(n);
}
bool is_ginductive_unpack(environment const & env, name const & n) {
    return get_extension(env).is_unpack(n);
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
