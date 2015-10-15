/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/environment.h"
#include "kernel/for_each_fn.h"
#include "library/reducible.h"
#include "library/module.h"

namespace lean {
struct decl_stats_ext : public environment_extension {
    name_set           m_class_instance; // set of all classes and class instances declared in some namespace
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

environment mark_class_instance_somewhere_core(environment const & env, name const & n) {
    decl_stats_ext ext = get_extension(env);
    ext.m_class_instance.insert(n);
    return update(env, ext);
}

static std::string * g_key = nullptr;

environment mark_class_instance_somewhere(environment const & env, name const & n) {
    environment new_env = mark_class_instance_somewhere_core(env, n);
    return module::add(new_env, *g_key, [=](environment const &, serializer & s) { s << n; });
}

bool is_class_instance_somewhere(environment const & env, name const & n) {
    return get_extension(env).m_class_instance.contains(n);
}

static void class_instance_mark_reader(deserializer & d, shared_environment & senv,
                                       std::function<void(asynch_update_fn const &)> &,
                                       std::function<void(delayed_update_fn const &)> &) {
    name n;
    d >> n;
    senv.update([=](environment const & env) -> environment {
            return mark_class_instance_somewhere_core(env, n);
        });
}

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
    g_ext = new decl_stats_ext_reg();
    g_key = new std::string("CIGLB");
    register_module_object_reader(*g_key, class_instance_mark_reader);
}

void finalize_decl_stats() {
    delete g_ext;
    delete g_key;
}
}
