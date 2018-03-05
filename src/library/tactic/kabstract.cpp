/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "library/module.h"
#include "library/head_map.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/occurrences.h"
#include "library/tactic/tactic_state.h"

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

struct key_equivalence_modification : public modification {
    LEAN_MODIFICATION("key_eqv")

    name m_n1, m_n2;

    key_equivalence_modification() {}
    key_equivalence_modification(name const & n1, name const & n2) : m_n1(n1), m_n2(n2) {}

    void perform(environment & env) const override {
        key_equivalence_ext ext = get_extension(env);
        ext.add_alias(m_n1, m_n2);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_n1 << m_n2;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name n1, n2;
        d >> n1 >> n2;
        return std::make_shared<key_equivalence_modification>(n1, n2);
    }
};

environment add_key_equivalence(environment const & env, name const & n1, name const & n2) {
    return module::add_and_perform(env, std::make_shared<key_equivalence_modification>(n1, n2));
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

expr kabstract(type_context_old & ctx, expr const & e, expr const & t, occurrences const & occs, bool unify) {
    lean_assert(closed(e));
    head_index idx1(t);
    key_equivalence_ext const & ext = get_extension(ctx.env());
    unsigned i = 1;
    unsigned t_nargs = get_app_num_args(t);
    return replace(e, [&](expr const & s, unsigned offset) {
            if (closed(s)) {
                head_index idx2(s);
                if (idx1.kind() == idx2.kind() &&
                    ext.is_eqv(idx1.get_name(), idx2.get_name()) &&
                    /* fail if same function application and different number of arguments */
                    (idx1.get_name() != idx2.get_name() || t_nargs == get_app_num_args(s)) &&
                    ((unify && ctx.unify(t, s)) || (!unify && ctx.match(t, s)))) {
                    if (occs.contains(i)) {
                        lean_trace("kabstract", scope_trace_env _(ctx.env(), ctx);
                                   tout() << "found target:\n" << s << "\n";);
                        i++;
                        return some_expr(mk_var(offset));
                    } else {
                        i++;
                    }
                }
            }
            return none_expr();
        }, occs.is_all());
}

bool kdepends_on(type_context_old & ctx, expr const & e, expr const & t) {
    bool found = false;
    head_index idx1(t);
    key_equivalence_ext const & ext = get_extension(ctx.env());
    unsigned t_nargs = get_app_num_args(t);
    for_each(e, [&](expr const & s, unsigned) {
            if (found) return false;
            if (closed(s)) {
                head_index idx2(s);
                if (idx1.kind() == idx2.kind() &&
                    ext.is_eqv(idx1.get_name(), idx2.get_name()) &&
                    /* fail if same function application and different number of arguments */
                    (idx1.get_name() != idx2.get_name() || t_nargs == get_app_num_args(s)) &&
                    ctx.is_def_eq(t, s)) {
                    found = true; return false;
                }
            }
            return true;
        });
    return found;
}

vm_obj tactic_kdepends_on(vm_obj const & e, vm_obj const & t, vm_obj const & md, vm_obj const & s) {
    try {
        type_context_old ctx = mk_type_context_for(s, md);
        return tactic::mk_success(mk_vm_bool(kdepends_on(ctx, to_expr(e), to_expr(t))), tactic::to_state(s));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, tactic::to_state(s));
    }
}

vm_obj tactic_kabstract(vm_obj const & e, vm_obj const & t, vm_obj const & md, vm_obj const & u, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    try {
        type_context_old ctx = mk_type_context_for(s, to_transparency_mode(md));
        auto a = kabstract(ctx, to_expr(e), to_expr(t), occurrences(), to_bool(u));
        return tactic::mk_success(to_obj(a), set_mctx(s, ctx.mctx()));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_kabstract() {
    register_trace_class("kabstract");
    g_ext           = new key_equivalence_ext_reg();
    key_equivalence_modification::init();
    DECLARE_VM_BUILTIN(name({"tactic", "kdepends_on"}), tactic_kdepends_on);
    DECLARE_VM_BUILTIN(name("tactic", "kabstract"),     tactic_kabstract);
}

void finalize_kabstract() {
    key_equivalence_modification::finalize();
    delete g_ext;
}
}
