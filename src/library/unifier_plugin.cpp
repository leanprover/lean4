/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lazy_list_fn.h"
#include "library/unifier_plugin.h"

namespace lean {
class binary_unifier_plugin_cell : public unifier_plugin_cell {
protected:
    unifier_plugin m_p1;
    unifier_plugin m_p2;
public:
    binary_unifier_plugin_cell(unifier_plugin const & p1, unifier_plugin const & p2):m_p1(p1), m_p2(p2) {}
    virtual bool delay_constraint(type_checker & tc, constraint const & c) const {
        return m_p1->delay_constraint(tc, c) || m_p2->delay_constraint(tc, c);
    }
};

class append_unifier_plugin_cell : public binary_unifier_plugin_cell {
public:
    append_unifier_plugin_cell(unifier_plugin const & p1, unifier_plugin const & p2):binary_unifier_plugin_cell(p1, p2) {}
    virtual lazy_list<constraints> solve(type_checker & tc, constraint const & c, name_generator && ngen) const {
        return append(m_p1->solve(tc, c, ngen.mk_child()), m_p2->solve(tc, c, ngen.mk_child()));
    }
};

class orelse_unifier_plugin_cell : public binary_unifier_plugin_cell {
public:
    orelse_unifier_plugin_cell(unifier_plugin const & p1, unifier_plugin const & p2):binary_unifier_plugin_cell(p1, p2) {}
    virtual lazy_list<constraints> solve(type_checker & tc, constraint const & c, name_generator && ngen) const {
        return orelse(m_p1->solve(tc, c, ngen.mk_child()), m_p2->solve(tc, c, ngen.mk_child()));
    }
};

unifier_plugin append(unifier_plugin const & p1, unifier_plugin const & p2) {
    return std::make_shared<append_unifier_plugin_cell>(p1, p2);
}

unifier_plugin orelse(unifier_plugin const & p1, unifier_plugin const & p2) {
    return std::make_shared<orelse_unifier_plugin_cell>(p1, p2);
}

static unifier_plugin noop_unifier_plugin() {
    class noop_unifier_plugin_cell : public unifier_plugin_cell {
    public:
        virtual lazy_list<constraints> solve(type_checker &, constraint const &, name_generator &&) const {
            return lazy_list<constraints>();
        }
        virtual bool delay_constraint(type_checker &, constraint const &) const { return false; }
    };
    return std::make_shared<noop_unifier_plugin_cell>();
}

struct unifier_plugin_ext : public environment_extension {
    unifier_plugin m_plugin;
    unifier_plugin_ext() {
        m_plugin = noop_unifier_plugin();
    }
};

struct unifier_plugin_ext_reg {
    unsigned m_ext_id;
    unifier_plugin_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<unifier_plugin_ext>()); }
};

static unifier_plugin_ext_reg * g_ext = nullptr;
static unifier_plugin_ext const & get_extension(environment const & env) {
    return static_cast<unifier_plugin_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, unifier_plugin_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<unifier_plugin_ext>(ext));
}

void initialize_unifier_plugin() {
    g_ext = new unifier_plugin_ext_reg();
}

void finalize_unifier_plugin() {
    delete g_ext;
}

environment set_unifier_plugin(environment const & env, unifier_plugin const & p) {
    unifier_plugin_ext ext = get_extension(env);
    ext.m_plugin = p;
    return update(env, ext);
}

unifier_plugin const & get_unifier_plugin(environment const & env) {
    return get_extension(env).m_plugin;
}
}
