/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr_maps.h"
#include "library/module.h"
#include "library/compiler/util.h"

namespace lean {
/* Cache closed term => global constant.
   TODO(Leo): use the to be implemented new module system. */
struct extract_closed_ext : public environment_extension {
    typedef rb_expr_map<name> cache;
    cache m_cache;
};

struct extract_closed_ext_reg {
    unsigned m_ext_id;
    extract_closed_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<extract_closed_ext>()); }
};

static extract_closed_ext_reg * g_ext = nullptr;
static extract_closed_ext const & get_extension(environment const & env) {
    return static_cast<extract_closed_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, extract_closed_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<extract_closed_ext>(ext));
}

/* Support for old module manager.
   Remark: this code will be deleted in the future */
struct ec_cache_modification : public modification {
    LEAN_MODIFICATION("ecc")

    expr      m_expr;
    name      m_name;

    ec_cache_modification(expr const & e, name const & n): m_expr(e), m_name(n) {}

    void perform(environment & env) const override {
        extract_closed_ext ext = get_extension(env);
        ext.m_cache.insert(m_expr, m_name);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_expr << m_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        expr e; name n;
        d >> e >> n;
        return std::make_shared<ec_cache_modification>(e, n);
    }
};

class extract_closed_fn {
    typedef std::unordered_map<name, bool, name_hash, name_eq> name2bool;
    environment         m_env;
    extract_closed_ext  m_ext;
    name_generator      m_ngen;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;
    unsigned            m_next_idx{1};
    name2bool           m_closed; // fvar id to boolean indicating whether it is a closed value or not
    name2bool           m_used_in_not_closed; // fvar id to boolean indicating whether it is used in cached value or not

    environment const & env() const { return m_env; }
    name_generator & ngen() { return m_ngen; }

    name next_name() {
        name r = name(m_base_name, "_closed").append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    expr visit(expr const & e) {
        // TODO(Leo):
        return e;
    }

public:
    extract_closed_fn(environment const & env):
        m_env(env), m_ext(get_extension(env)) {
    }

    pair<environment, comp_decls> operator()(comp_decl const & d) {
        m_base_name = d.fst();
        expr new_v = visit(d.snd());
        comp_decl new_d(d.fst(), new_v);
        environment new_env = update(env(), m_ext);
        return mk_pair(new_env, comp_decls(new_d, comp_decls(m_new_decls)));
    }
};

pair<environment, comp_decls> extract_closed_core(environment const & env, comp_decl const & d) {
    return extract_closed_fn(env)(d);
}

pair<environment, comp_decls> extract_closed(environment env, comp_decls const & ds) {
    comp_decls r;
    for (comp_decl const & d : ds) {
        comp_decls new_ds;
        std::tie(env, new_ds) = extract_closed_core(env, d);
        r = append(r, new_ds);
    }
    return mk_pair(env, r);
}

void initialize_extract_closed() {
    g_ext = new extract_closed_ext_reg();
    ec_cache_modification::init();
}

void finalize_extract_closed() {
    ec_cache_modification::finalize();
    delete g_ext;
}
}
