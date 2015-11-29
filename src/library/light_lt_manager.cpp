/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/light_lt_manager.h"
#include "util/sstream.h"
#include "util/name_set.h"
#include "util/safe_arith.h"
#include "kernel/error_msgs.h"
#include "kernel/instantiate.h"
#include "library/scoped_ext.h"
#include <string>

namespace lean {

static unsigned add_weight(unsigned num, expr const * args) {
    unsigned r = 0;
    for (unsigned i = 0; i < num; i++)
        r = safe_add(r, get_weight(args[i]));
    return r;
}

unsigned light_lt_manager::get_weight_core(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:  case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Meta: case expr_kind::Local:
        return 1;
    case expr_kind::Lambda: case expr_kind::Pi:
        return safe_add(1, safe_add(get_weight(binding_domain(e)), get_weight(binding_body(e))));
    case expr_kind::Macro:
        return safe_add(1, add_weight(macro_num_args(e), macro_args(e)));
    case expr_kind::App:
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        if (is_constant(fn)) {
            unsigned const * light_arg = m_lrs.find(const_name(fn));
            if (light_arg && args.size() > *light_arg) return get_weight(args[*light_arg]);
        }
        return safe_add(1, safe_add(get_weight(app_fn(e)), get_weight(app_arg(e))));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

unsigned light_lt_manager::get_weight(expr const & e) {
    auto it = m_weight_cache.find(e);
    if (it != m_weight_cache.end()) return it->second;
    unsigned w = get_weight_core(e);
    m_weight_cache.insert(mk_pair(e, w));
    return w;
}

bool light_lt_manager::is_lt(expr const & a, expr const & b) {
    if (is_eqp(a, b)) return false;
    unsigned wa = get_weight(a);
    unsigned wb = get_weight(b);
    if (wa < wb)                         return true;
    if (wa > wb)                         return false;
    if (is_constant(get_app_fn(a))) {
        unsigned const * light_arg = m_lrs.find(const_name(get_app_fn(a)));
        if (light_arg) {
            buffer<expr> args;
            get_app_args(a, args);
            if (args.size() > *light_arg) return is_lt(args[*light_arg], b);
        }
    }
    if (is_constant(get_app_fn(b))) {
        unsigned const * light_arg = m_lrs.find(const_name(get_app_fn(b)));
        if (light_arg) {
            buffer<expr> args;
            get_app_args(b, args);
            if (args.size() > *light_arg) return !is_lt(args[*light_arg], a);
        }
    }
    if (a.kind() != b.kind())            return a.kind() < b.kind();
    if (a == b)                          return false;
    switch (a.kind()) {
    case expr_kind::Var:
        return var_idx(a) < var_idx(b);
    case expr_kind::Constant:
        if (const_name(a) != const_name(b))
            return const_name(a) < const_name(b);
        else
            return ::lean::is_lt(const_levels(a), const_levels(b), false);
    case expr_kind::App:
        if (app_fn(a) != app_fn(b))
            return is_lt(app_fn(a), app_fn(b));
        else
            return is_lt(app_arg(a), app_arg(b));
    case expr_kind::Lambda: case expr_kind::Pi:
        if (binding_domain(a) != binding_domain(b))
            return is_lt(binding_domain(a), binding_domain(b));
        else
            return is_lt(binding_body(a), binding_body(b));
    case expr_kind::Sort:
        return ::lean::is_lt(sort_level(a), sort_level(b), false);
    case expr_kind::Local: case expr_kind::Meta:
        if (mlocal_name(a) != mlocal_name(b))
            return mlocal_name(a) < mlocal_name(b);
        else
            return is_lt(mlocal_type(a), mlocal_type(b));
    case expr_kind::Macro:
        if (macro_def(a) != macro_def(b))
            return macro_def(a) < macro_def(b);
        if (macro_num_args(a) != macro_num_args(b))
            return macro_num_args(a) < macro_num_args(b);
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            if (macro_arg(a, i) != macro_arg(b, i))
                return is_lt(macro_arg(a, i), macro_arg(b, i));
        }
        return false;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct lrs_state {
    light_rule_set           m_lrs;
    void add(environment const &, io_state const &, name const & id, unsigned light_arg) {
        m_lrs.insert(id, light_arg);
    }
};

struct lrs_entry {
    name     m_id;
    unsigned m_light_arg;
    lrs_entry() {}
    lrs_entry(name const & id, unsigned light_arg): m_id(id), m_light_arg(light_arg) { }
};

struct lrs_config {
    typedef lrs_entry  entry;
    typedef lrs_state  state;
    static void add_entry(environment const & env, io_state const & ios, state & s, entry const & e) {
        s.add(env, ios, e.m_id, e.m_light_arg);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_id << e.m_light_arg;
    }
    static entry read_entry(deserializer & d) {
        entry e; d >> e.m_id >> e.m_light_arg; return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.m_id.hash());
    }
};

template class scoped_ext<lrs_config>;
typedef scoped_ext<lrs_config> lrs_ext;

environment add_light_rule(environment const & env, name const & id, unsigned light_arg,  bool persistent) {
    return lrs_ext::add_entry(env, get_dummy_ios(), lrs_entry(id, light_arg), persistent);
}

optional<unsigned> is_light_rule(environment const & env, name const & n) {
    unsigned const * light_arg = lrs_ext::get_state(env).m_lrs.find(n);
    if (light_arg) return optional<unsigned>(*light_arg);
    else return optional<unsigned>();
}

light_rule_set get_light_rule_set(environment const & env) {
    return lrs_ext::get_state(env).m_lrs;
}

light_rule_set get_light_rule_set(environment const & env, io_state const &, name const & ns) {
    light_rule_set lrs;
    list<lrs_entry> const * entries = lrs_ext::get_entries(env, ns);
    if (entries) {
        for (auto const & e : *entries) {
            lrs.insert(e.m_id, e.m_light_arg);
        }
    }
    return lrs;
}

io_state_stream const & operator<<(io_state_stream const & out, light_rule_set const & lrs) {
    out << "light rules\n";
    lrs.for_each([&](name const & id, unsigned const & light_arg) {
            out << id << " @ " << light_arg << "\n";
        });
    return out;
}

void initialize_light_rule_set() {
    g_class_name = new name("lrs");
    g_key        = new std::string("lrs");
    lrs_ext::initialize();
}

void finalize_light_rule_set() {
    lrs_ext::finalize();
    delete g_key;
    delete g_class_name;
}

}
