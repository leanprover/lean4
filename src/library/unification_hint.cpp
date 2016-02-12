/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <string>
#include "util/sexpr/format.h"
#include "kernel/expr.h"
#include "kernel/error_msgs.h"
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/unification_hint.h"
#include "library/util.h"
#include "library/expr_lt.h"
#include "library/scoped_ext.h"

namespace lean {

/* Unification hints */

unification_hint::unification_hint(expr const & lhs, expr const & rhs, list<expr_pair> const & constraints, unsigned num_vars):
    m_lhs(lhs), m_rhs(rhs), m_constraints(constraints), m_num_vars(num_vars) {}

int unification_hint_cmp::operator()(unification_hint const & uh1, unification_hint const & uh2) const {
    if (uh1.get_lhs() != uh2.get_lhs()) {
        return expr_quick_cmp()(uh1.get_lhs(), uh2.get_lhs());
    } else if (uh1.get_rhs() != uh2.get_rhs()) {
        return expr_quick_cmp()(uh1.get_rhs(), uh2.get_rhs());
    } else {
        auto it1 = uh1.get_constraints().begin();
        auto it2 = uh2.get_constraints().begin();
        auto end1 = uh1.get_constraints().end();
        auto end2 = uh2.get_constraints().end();
        for (; it1 != end1 && it2 != end2; ++it1, ++it2) {
            if (unsigned cmp = expr_pair_quick_cmp()(*it1, *it2)) return cmp;
        }
        return 0;
    }
}

/* Environment extension */

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct unification_hint_state {
    unification_hints m_hints;
    name_map<unsigned> m_decl_names_to_prio; // Note: redundant but convenient

    void validate_type(expr const & decl_type) {
        expr type = decl_type;
        while (is_pi(type)) type = binding_body(type);
        if (!is_app_of(type, get_unification_hint_name(), 0)) {
            throw exception("invalid unification hint, must return element of type `unification hint`");
        }
    }

    void register_hint(name const & decl_name, expr const & value, unsigned priority) {
        m_decl_names_to_prio.insert(decl_name, priority);

        expr e_hint = value;
        unsigned num_vars = 0;
        while (is_lambda(e_hint)) {
            e_hint = binding_body(e_hint);
            num_vars++;
        }

        if (!is_app_of(e_hint, get_unification_hint_mk_name(), 2)) {
            throw exception("invalid unification hint, body must be application of 'unification_hint.mk' to two arguments");
        }

        // e_hint := unification_hint.mk pattern constraints
        expr e_pattern = app_arg(app_fn(e_hint));
        expr e_constraints = app_arg(e_hint);

        // pattern := unification_constraint.mk _ lhs rhs
        expr e_pattern_lhs = app_arg(app_fn(e_pattern));
        expr e_pattern_rhs = app_arg(e_pattern);

        expr e_pattern_lhs_fn = get_app_fn(e_pattern_lhs);
        expr e_pattern_rhs_fn = get_app_fn(e_pattern_rhs);

        if (!is_constant(e_pattern_lhs_fn) || !is_constant(e_pattern_rhs_fn)) {
            throw exception("invalid unification hint, the heads of both sides of pattern must be constants");
        }

        name_pair key = mk_pair(const_name(e_pattern_lhs_fn), const_name(e_pattern_rhs_fn));

        buffer<expr_pair> constraints;
        while (is_app_of(e_constraints, get_list_cons_name(), 3)) {
            // e_constraints := cons _ constraint rest
            expr e_constraint = app_arg(app_fn(e_constraints));
            expr e_constraint_lhs = app_arg(app_fn(e_constraint));
            expr e_constraint_rhs = app_arg(e_constraint);
            constraints.push_back(mk_pair(e_constraint_lhs, e_constraint_rhs));
            e_constraints = app_arg(e_constraints);
        }

        if (!is_app_of(e_constraints, get_list_nil_name(), 1)) {
            throw exception("invalid unification hint, must provide list of constraints explicitly");
        }

        unification_hint hint(e_pattern_lhs, e_pattern_rhs, to_list(constraints), num_vars);
        unification_hint_queue q;
        if (auto const & q_ptr = m_hints.find(key)) q = *q_ptr;
        q.insert(hint, priority);
        m_hints.insert(key, q);
    }
};

struct unification_hint_entry {
    name m_decl_name;
    unsigned m_priority;
    unification_hint_entry(name const & decl_name, unsigned priority):
        m_decl_name(decl_name), m_priority(priority) {}
};

struct unification_hint_config {
    typedef unification_hint_entry entry;
    typedef unification_hint_state state;

    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        declaration decl = env.get(e.m_decl_name);
        s.validate_type(decl.get_type());
        // Note: only definitions should be tagged as [unify], so if it is not a definition,
        // there must have been an error when processing the definition. We return immediately
        // so as not to hide the original error.
        // TODO(dhs): the downside to this approach is that a [unify] tag on an actual axiom will be silently ignored.
        if (decl.is_definition()) s.register_hint(e.m_decl_name, decl.get_value(), e.m_priority);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_decl_name << e.m_priority;
    }
    static entry read_entry(deserializer & d) {
        name decl_name; unsigned prio;
        d >> decl_name >> prio;
        return entry(decl_name, prio);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(e.m_decl_name.hash(), e.m_priority));
    }
};

typedef scoped_ext<unification_hint_config> unification_hint_ext;

environment add_unification_hint(environment const & env, io_state const & ios, name const & decl_name, unsigned prio, name const & ns, bool persistent) {
    return unification_hint_ext::add_entry(env, ios, unification_hint_entry(decl_name, prio), ns, persistent);
}

bool is_unification_hint(environment const & env, name const & decl_name) {
    return unification_hint_ext::get_state(env).m_decl_names_to_prio.contains(decl_name);
}

unification_hints get_unification_hints(environment const & env) {
    return unification_hint_ext::get_state(env).m_hints;
}

unification_hints get_unification_hints(environment const & env, name const & ns) {
    list<unification_hint_entry> const * entries = unification_hint_ext::get_entries(env, ns);
    unification_hint_state s;
    if (entries) {
        for (auto const & e : *entries) {
            declaration decl = env.get(e.m_decl_name);
            s.register_hint(e.m_decl_name, decl.get_value(), e.m_priority);
        }
    }
    return s.m_hints;
}

void get_unification_hints(environment const & env, name const & n1, name const & n2, buffer<unification_hint> & uhints) {
    unification_hints hints = unification_hint_ext::get_state(env).m_hints;
    if (auto const & q_ptr = hints.find(mk_pair(n1, n2))) {
        q_ptr->to_buffer(uhints);
    }
    if (auto const & q_ptr = hints.find(mk_pair(n2, n1))) {
        q_ptr->to_buffer(uhints);
    }
}

/* Pretty-printing */

// TODO(dhs): I may not be using all the formatting functions correctly.
format unification_hint::pp(unsigned prio, formatter const & fmt) const {
    format r;
    if (prio != LEAN_DEFAULT_PRIORITY)
        r += paren(format(prio)) + space();
    format r1 = fmt(get_lhs()) + space() + format("=?=") + pp_indent_expr(fmt, get_rhs());
    r1 += space() + lcurly();
    r += group(r1);
    for_each(m_constraints, [&](expr_pair p) {
            r += fmt(p.first) + space() + format("=?=");
            r += space() + fmt(p.second) + comma() + space();
        });
    r += rcurly();
    return r;
}

format pp_unification_hints(unification_hints const & hints, formatter const & fmt, format const & header) {
    format r;
    r += format("unification hints");
    r += header + colon() + line();
    hints.for_each([&](name_pair const & names, unification_hint_queue const & q) {
            q.for_each([&](unification_hint const & hint) {
                    r += lp() + format(names.first) + comma() + space() + format(names.second) + rp() + space();
                    r += hint.pp(*q.get_prio(hint), fmt) + line();
                });
        });
    return r;
}

void initialize_unification_hint() {
    g_class_name    = new name("unification_hint");
    g_key           = new std::string("UNIFICATION_HINT");

    unification_hint_ext::initialize();

    register_prio_attribute("unify", "unification hint",
                            add_unification_hint,
                            is_unification_hint,
                            [](environment const & env, name const & decl_name) {
                                if (auto p = unification_hint_ext::get_state(env).m_decl_names_to_prio.find(decl_name))
                                    return *p;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });
}

void finalize_unification_hint() {
    unification_hint_ext::finalize();
    delete g_key;
    delete g_class_name;
}
}
