/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/for_each_fn.h"
#include "library/reducible.h"

namespace lean {
struct decl_stats_ext : public environment_extension {
    name_map<unsigned> m_num_occs;
    name_map<name_set> m_use_set;
    name_map<name_set> m_used_by_set;

    void inc_num_occs(name const & n) {
        if (auto v = m_num_occs.find(n)) {
            m_num_occs.insert(n, *v+1);
        } else {
            m_num_occs.insert(n, 1);
        }
    }

    static void updt(name_map<name_set> & s, name const & k, name const & v) {
        name_set new_set_v;
        if (auto set_v = s.find(k))
            new_set_v = *set_v;
        new_set_v.insert(v);
        s.insert(k, new_set_v);
    }

    void updt(name const & user, name const & used) {
        inc_num_occs(used);
        updt(m_use_set,     user, used);
        updt(m_used_by_set, used, user);
    }
};

struct decl_stats_ext_reg {
    unsigned m_ext_id;
    decl_stats_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<decl_stats_ext>()); }
};

static decl_stats_ext_reg * g_ext = nullptr;
static decl_stats_ext const & get_extension(environment const & env) {
    return static_cast<decl_stats_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, decl_stats_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<decl_stats_ext>(ext));
}

class update_decl_stats_fn {
    environment const & m_env;
    decl_stats_ext      m_ext;
    name                m_name;
    name_set            m_visited;
    name_predicate      m_not_reducible_pred;

    void visit(expr const & e) {
        for_each(e, [&](expr const & e, unsigned) {
                if (!is_constant(e))
                    return true;
                name const & n = const_name(e);
                if (m_visited.contains(n))
                    return true;
                m_visited.insert(n);
                if (m_not_reducible_pred(n)) {
                    m_ext.updt(m_name, n);
                } else {
                    // pretend the reducible definition was expanded.
                    declaration d = m_env.get(n);
                    visit(d.get_value());
                }
                return true;
            });
    }

public:
    update_decl_stats_fn(environment const & env):
        m_env(env),
        m_ext(get_extension(env)),
        m_not_reducible_pred(mk_not_reducible_pred(env)) {}

    environment operator()(declaration const & d) {
        m_name = d.get_name();
        visit(d.get_type());
        return update(m_env, m_ext);
    }
};

environment update_decl_stats(environment const & env, declaration const & d) {
    return update_decl_stats_fn(env)(d);
}

unsigned get_num_occs(environment const & env, name const & n) {
    if (auto v = get_extension(env).m_num_occs.find(n))
        return *v;
    else
        return 0;
}

name_set get_use_set(environment const & env, name const & n) {
    if (auto v = get_extension(env).m_use_set.find(n))
        return *v;
    else
        return name_set();
}

name_set get_used_by_set(environment const & env, name const & n) {
    if (auto v = get_extension(env).m_used_by_set.find(n))
        return *v;
    else
        return name_set();
}

void initialize_decl_stats() {
    g_ext     = new decl_stats_ext_reg();
}

void finalize_decl_stats() {
    delete g_ext;
}
}
