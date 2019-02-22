/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/module.h"
#include "library/annotation.h"
#include "library/compiler/util.h"

namespace lean {
static name * g_borrowed = nullptr;

expr mk_borrowed(expr const & e) { return mk_annotation(*g_borrowed, e); }
bool is_borrowed(expr const & e) { return is_annotation(e, *g_borrowed); }
expr const & get_borrowed_arg(expr const & e) { lean_assert(is_borrowed(e)); return get_annotation_arg(e); }

struct borrowed_info {
    list<bool> m_borrowed_args;
    bool       m_borrowed_res;
};

/* Inferred borrowed annotations cache. */
struct borrowed_ext : public environment_extension {
    typedef name_map<borrowed_info> cache;
    cache m_cache;
};

struct borrowed_ext_reg {
    unsigned m_ext_id;
    borrowed_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<borrowed_ext>()); }
};

static borrowed_ext_reg * g_ext = nullptr;
static borrowed_ext const & get_extension(environment const & env) {
    return static_cast<borrowed_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, borrowed_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<borrowed_ext>(ext));
}

/* Support for old module manager.
   Remark: this code will be deleted in the future */
struct borrowed_modification : public modification {
    LEAN_MODIFICATION("borrowed");

    name          m_fn;
    borrowed_info m_info;

    borrowed_modification(name const & fn, borrowed_info const & info):m_fn(fn), m_info(info) {}

    void perform(environment & env) const override {
        borrowed_ext ext = get_extension(env);
        ext.m_cache.insert(m_fn, m_info);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_fn << m_info.m_borrowed_res;
        write_list(s, m_info.m_borrowed_args);
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name fn; borrowed_info info;
        d >> fn >> info.m_borrowed_res;
        info.m_borrowed_args = read_list<bool>(d);
        return std::make_shared<borrowed_modification>(fn, info);
    }
};

bool get_inferred_borrowed_info(environment const & env, name const & fn, buffer<bool> & borrowed_args, bool & borrowed_res) {
    borrowed_ext const & ext = get_extension(env);
    if (borrowed_info const * info = ext.m_cache.find(fn)) {
        to_buffer(info->m_borrowed_args, borrowed_args);
        borrowed_res = info->m_borrowed_res;
        return true;
    } else {
        return false;
    }
}

environment infer_borrowed_annotations(environment const & env, buffer<comp_decl> const &) {
    // TODO(Leo)
    return env;
}

void initialize_borrowed_annotation() {
    g_borrowed = new name("borrowed");
    register_annotation(*g_borrowed);
    g_ext = new borrowed_ext_reg();
    borrowed_modification::init();
}

void finalize_borrowed_annotation() {
    delete g_borrowed;
    delete g_ext;
    borrowed_modification::finalize();
}
}
