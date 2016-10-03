/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "kernel/replace_fn.h"
#include "library/module.h"
#include "library/head_map.h"
#include "library/type_context.h"
#include "library/tactic/occurrences.h"

namespace lean {
struct key_equivalence_ext : public environment_extension {
    typedef unsigned node_ref;
    struct node {
        node_ref m_parent;
        unsigned m_rank;
    };

    unsigned           m_next_idx;
    unsigned_map<node> m_nodes;
    name_map<node_ref> m_to_node;

    node_ref mk_node() {
        node_ref r = m_next_idx;
        m_next_idx++;
        node n;
        n.m_parent = r;
        n.m_rank   = 0;
        m_nodes.insert(r, n);
        return r;
    }

    node_ref find(node_ref n) const {
        while (true) {
            node_ref p = m_nodes.find(n)->m_parent;
            if (p == n)
                return p;
            n = p;
        }
    }

    void merge(node_ref n1, node_ref n2) {
        node_ref r1 = find(n1);
        node_ref r2 = find(n2);
        if (r1 != r2) {
            node ref1 = *m_nodes.find(r1);
            node ref2 = *m_nodes.find(r2);
            if (ref1.m_rank < ref2.m_rank) {
                ref1.m_parent = r2;
                m_nodes.insert(r1, ref1);
            } else if (ref1.m_rank > ref2.m_rank) {
                ref2.m_parent = r1;
                m_nodes.insert(r2, ref2);
            } else {
                ref2.m_parent = r1;
                ref1.m_rank++;
                m_nodes.insert(r2, ref2);
            }
        }
    }

    node_ref to_node(name const & n) {
        if (auto it = m_to_node.find(n))
            return *it;
        node_ref r = mk_node();
        m_to_node.insert(n, r);
        return r;
    }

    key_equivalence_ext() {}

    void add_alias(name const & n1, name const & n2) {
        merge(to_node(n1), to_node(n2));
    }

    bool is_eqv(name const & n1, name const & n2) const {
        if (n1 == n2) return true;
        auto it1 = m_to_node.find(n1);
        if (!it1) return false;
        auto it2 = m_to_node.find(n2);
        if (!it2) return false;
        return find(*it1) == find(*it2);
    }
};

struct key_equivalence_ext_reg {
    unsigned m_ext_id;
    key_equivalence_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<key_equivalence_ext>()); }
};

static key_equivalence_ext_reg * g_ext = nullptr;
static key_equivalence_ext const & get_extension(environment const & env) {
    return static_cast<key_equivalence_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, key_equivalence_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<key_equivalence_ext>(ext));
}

static std::string * g_key_equivalence_key = nullptr;

environment add_key_equivalence(environment const & env, name const & n1, name const & n2) {
    key_equivalence_ext ext = get_extension(env);
    ext.add_alias(n1, n2);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_key_equivalence_key, [=](environment const &, serializer & s) { s << n1 << n2; });
}

bool is_key_equivalent(environment const & env, name const & n1, name const & n2) {
    return get_extension(env).is_eqv(n1, n2);
}

void for_each_key_equivalence(environment const & env, std::function<void(buffer<name> const &)> const & fn) {
    key_equivalence_ext const & ext = get_extension(env);
    name_set visited;
    ext.m_to_node.for_each([&](name const & n1, key_equivalence_ext::node_ref const & r1) {
            if (visited.contains(n1)) return;
            buffer<name> eqv;
            key_equivalence_ext::node_ref root1 = ext.find(r1);
            ext.m_to_node.for_each([&](name const & n2, key_equivalence_ext::node_ref const & r2) {
                    if (ext.find(r2) == root1) {
                        visited.insert(n2);
                        eqv.push_back(n2);
                    }
                });
            fn(eqv);
        });
}

static void key_equivalence_reader(deserializer & d, shared_environment & senv,
                                   std::function<void(asynch_update_fn const &)> &,
                                   std::function<void(delayed_update_fn const &)> &) {
    name n1, n2;
    d >> n1 >> n2;
    senv.update([=](environment const & env) -> environment {
            key_equivalence_ext ext = get_extension(env);
            ext.add_alias(n1, n2);
            return update(env, ext);
        });
}

expr kabstract(type_context & ctx, expr const & e, expr const & t, occurrences const & occs) {
    lean_assert(closed(e));
    head_index idx1(t);
    key_equivalence_ext const & ext = get_extension(ctx.env());
    unsigned i = 1;
    return replace(e, [&](expr const & s, unsigned offset) {
            if (closed(s)) {
                head_index idx2(s);
                if (idx1.kind() == idx2.kind() &&
                    ext.is_eqv(idx1.get_name(), idx2.get_name()) &&
                    /* fail if same function application and different number of arguments */
                    (idx1.get_name() != idx2.get_name() || get_app_num_args(t) == get_app_num_args(s)) &&
                    ctx.is_def_eq(t, s)) {
                    if (occs.contains(i)) {
                        i++;
                        return some_expr(mk_var(offset));
                    } else {
                        i++;
                    }
                }
            }
            return none_expr();
        });
}

void initialize_kabstract() {
    g_ext           = new key_equivalence_ext_reg();
    g_key_equivalence_key = new std::string("keyeqv");
    register_module_object_reader(*g_key_equivalence_key, key_equivalence_reader);
}

void finalize_kabstract() {
    delete g_key_equivalence_key;
    delete g_ext;
}
}
