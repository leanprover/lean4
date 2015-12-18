/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <string>
#include "util/sstream.h"
#include "kernel/error_msgs.h"
#include "kernel/instantiate.h"
#include "library/scoped_ext.h"
#include "library/attribute_manager.h"
#include "library/blast/backward/backward_rule_set.h"

namespace lean {

using blast::backward_rule;
using blast::backward_rule_set;
using blast::gexpr;
using std::function;

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct brs_state {
    backward_rule_set        m_backward_rule_set;
    name_set                 m_names;
    void add(environment const & env, options const & o, name const & cname, unsigned prio) {
        default_type_context tctx(env, o);
        m_backward_rule_set.insert(tctx, cname, prio);
        m_names.insert(cname);
    }
};

struct brs_entry {
    name     m_name;
    unsigned m_priority;
    brs_entry() {}
    brs_entry(name const & n, unsigned prio): m_name(n), m_priority(prio) { }
};

struct brs_config {
    typedef brs_entry  entry;
    typedef brs_state  state;
    static void add_entry(environment const & env, io_state const & ios, state & s, entry const & e) {
        s.add(env, ios.get_options(), e.m_name, e.m_priority);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_name << e.m_priority;
    }
    static entry read_entry(deserializer & d) {
        entry e; d >> e.m_name >> e.m_priority; return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.m_name.hash());
    }
};

template class scoped_ext<brs_config>;
typedef scoped_ext<brs_config> brs_ext;

environment add_backward_rule(environment const & env, name const & n, unsigned priority, name const & ns, bool persistent) {
    return brs_ext::add_entry(env, get_dummy_ios(), brs_entry(n, priority), ns, persistent);
}

bool is_backward_rule(environment const & env, name const & n) {
    return brs_ext::get_state(env).m_names.contains(n);
}

backward_rule_set get_backward_rule_set(environment const & env) {
    return brs_ext::get_state(env).m_backward_rule_set;
}

backward_rule_set get_backward_rule_sets(environment const & env, options const & o, name const & ns) {
    backward_rule_set brs;
    list<brs_entry> const * entries = brs_ext::get_entries(env, ns);
    if (entries) {
        for (auto const & e : *entries) {
            default_type_context tctx(env, o);
            brs.insert(tctx, e.m_name, e.m_priority);
        }
    }
    return brs;
}

io_state_stream const & operator<<(io_state_stream const & out, backward_rule_set const & brs) {
    out << "backward rules\n";
    brs.for_each([&](head_index const & head_idx, backward_rule const & r) {
            out << head_idx << " ==> " << r.get_proof().to_bare_expr() << "\n";
        });
    return out;
}

namespace blast {

bool operator==(backward_rule const & r1, backward_rule const & r2) {
    return r1.get_proof() == r2.get_proof();
}

void backward_rule_set::insert(type_context & tctx, name const & id, gexpr const & proof, expr const & _thm, unsigned prio) {
    expr thm = tctx.whnf(_thm);
    while (is_pi(thm)) {
        expr local = tctx.mk_tmp_local(binding_domain(thm), binding_info(thm));
        thm = tctx.whnf(instantiate(binding_body(thm), local));
    }
    m_set.insert(head_index(thm), backward_rule(id, proof, prio));
}

void backward_rule_set::insert(type_context & tctx, name const & name, unsigned prio) {
    gexpr proof(tctx.env(), name);
    declaration const & d = tctx.env().get(name);
    insert(tctx, name, proof, d.get_type(), prio);
}

void backward_rule_set::erase(name_set const & ids) {
    // This method is not very smart and doesn't use any indexing or caching.
    // So, it may be a bottleneck in the future
    buffer<pair<head_index, backward_rule> > to_delete;
    for_each([&](head_index const & h, backward_rule const & r) {
            if (ids.contains(r.get_id())) {
                to_delete.push_back(mk_pair(h, r));
            }
        });
    for (auto const & hr : to_delete) {
        m_set.erase(hr.first, hr.second);
    }
}

void backward_rule_set::erase(name const & id) {
    name_set ids;
    ids.insert(id);
    erase(ids);
}

void backward_rule_set::for_each(std::function<void(head_index const & h, backward_rule const & r)> const & fn) const {
    m_set.for_each_entry(fn);
}

list<gexpr> backward_rule_set::find(head_index const & h) const {
    list<backward_rule> const * rule_list = m_set.find(h);
    if (!rule_list) return list<gexpr>();
    return map2<gexpr, backward_rule, function<gexpr(backward_rule)>>(*rule_list, [&](backward_rule const & r) { return r.get_proof(); });
}

void initialize_backward_rule_set() {
    g_class_name = new name("brs");
    g_key        = new std::string("brs");
    brs_ext::initialize();
    register_prio_attribute("intro", "backward chaining",
                            [](environment const & env, io_state const &, name const & d, unsigned prio, name const & ns, bool persistent) {
                                return add_backward_rule(env, d, prio, ns, persistent);
                            },
                            is_backward_rule,
                            [](environment const &, name const &) {
                                // TODO(Leo): fix it after we refactor backward_rule_set
                                return LEAN_DEFAULT_PRIORITY;
                            });
}

void finalize_backward_rule_set() {
    brs_ext::finalize();
    delete g_key;
    delete g_class_name;
}
}
}
