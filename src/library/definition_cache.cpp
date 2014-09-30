/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/for_each_fn.h"
#include "library/placeholder.h"
#include "library/kernel_serializer.h"
#include "library/definition_cache.h"
#include "library/fingerprint.h"

namespace lean {
/** \brief Similar to expr_eq_fn, but allows different placeholders
    with different names. We cannot use the hashcode to speedup comparasion.
*/
class expr_eq_modulo_placeholders_fn {
    name_map<name> m_map; // for comparing placeholder names

    bool compare(name const & a, name const & b, bool placeholders) {
        if (!placeholders) {
            return a == b;
        } else if (auto it = m_map.find(a)) {
            return *it == b;
        } else {
            m_map.insert(a, b);
            return true;
        }
    }

    bool compare(level const & l1, level const & l2) {
        if (kind(l1) != kind(l2)) return false;
        if (is_eqp(l1, l2))       return true;
        bool placeholders = is_placeholder(l1) && is_placeholder(l2);
        switch (kind(l1)) {
        case level_kind::Zero:
            return true;
        case level_kind::Param:
            return compare(param_id(l1), param_id(l2), placeholders);
        case level_kind::Global:
            return compare(global_id(l1), global_id(l2), placeholders);
        case level_kind::Meta:
            return compare(meta_id(l1), meta_id(l2), placeholders);
        case level_kind::Max:
            if (get_depth(l1) != get_depth(l2))
                return false;
            return
                compare(max_lhs(l1), max_lhs(l2)) &&
                compare(max_rhs(l1), max_rhs(l2));
        case level_kind::IMax:
            if (get_depth(l1) != get_depth(l2))
                return false;
            return
                compare(imax_lhs(l1), imax_lhs(l2)) &&
                compare(imax_rhs(l1), imax_rhs(l2));
        case level_kind::Succ:
            if (get_depth(l1) != get_depth(l2))
                return false;
            return
                is_explicit(l1) == is_explicit(l2) &&
                (is_explicit(l1) || compare(succ_of(l1), succ_of(l2)));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    bool compare(levels const & ls1, levels const & ls2) {
        return ::lean::compare(ls1, ls2,
                               [&](level const & l1, level const & l2) { return compare(l1, l2); });
    }

    bool compare(expr const & a, expr const & b) {
        if (is_eqp(a, b))                   return true;
        if (a.kind() != b.kind())           return false;
        if (get_weight(a) != get_weight(b)) return false;
        check_system("expression equality modulo placeholder test");
        bool placeholders = is_placeholder(a) && is_placeholder(b);
        switch (a.kind()) {
        case expr_kind::Var:
            return var_idx(a) == var_idx(b);
        case expr_kind::Constant:
            return
                compare(const_name(a), const_name(b), placeholders) &&
                compare(const_levels(a), const_levels(b));
        case expr_kind::Meta:
            return
                compare(mlocal_name(a), mlocal_name(b), placeholders) &&
                compare(mlocal_type(a), mlocal_type(b));
        case expr_kind::Local:
            return
                compare(mlocal_name(a), mlocal_name(b), placeholders) &&
                compare(mlocal_type(a), mlocal_type(b)) &&
                local_pp_name(a) == local_pp_name(b) &&
                local_info(a) == local_info(b);
        case expr_kind::App:
            return
                compare(app_fn(a), app_fn(b)) &&
                compare(app_arg(a), app_arg(b));
        case expr_kind::Lambda: case expr_kind::Pi:
            return
                compare(binding_domain(a), binding_domain(b)) &&
                compare(binding_body(a), binding_body(b)) &&
                binding_info(a) == binding_info(b);
        case expr_kind::Sort:
            return compare(sort_level(a), sort_level(b));
        case expr_kind::Macro:
            if (macro_def(a) != macro_def(b) || macro_num_args(a) != macro_num_args(b))
                return false;
            for (unsigned i = 0; i < macro_num_args(a); i++) {
                if (!compare(macro_arg(a, i), macro_arg(b, i)))
                    return false;
            }
            return true;
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

public:
    expr_eq_modulo_placeholders_fn() {}
    bool operator()(expr const & a, expr const & b) { return compare(a, b); }
};

definition_cache::entry::entry(expr const & pre_t, expr const & pre_v,
                               level_param_names const & ps, expr const & t, expr const & v,
                               dependencies const & deps, uint64 fingerprint):
    m_pre_type(pre_t), m_pre_value(pre_v), m_params(ps),
    m_type(t), m_value(v), m_dependencies(deps), m_fingerprint(fingerprint) {}

definition_cache::definition_cache() {}

void definition_cache::load(std::istream & in) {
    lock_guard<mutex> lc(m_mutex);
    deserializer d(in);
    unsigned num;
    d >> num;
    for (unsigned i = 0; i < num; i++) {
        name n;
        level_param_names ls;
        expr pre_type, pre_value, type, value;
        d >> n >> pre_type >> pre_value >> ls >> type >> value;
        dependencies deps;
        unsigned num;
        d >> num;
        for (unsigned i = 0; i < num; i++) {
            name n; unsigned h;
            d >> n >> h;
            deps.insert(n, h);
        }
        uint64 fingerprint;
        d >> fingerprint;
        add_core(n, pre_type, pre_value, ls, type, value, deps, fingerprint);
    }
}

void definition_cache::collect_dependencies(environment const & env, expr const & e, dependencies & deps) {
    for_each(e, [&](expr const & e, unsigned) {
            if (!is_constant(e))
                return true;
            name const & n = const_name(e);
            if (deps.contains(n))
                return true;
            auto d = env.find(n);
            if (!d)
                return true;
            deps.insert(n, hash_bi(d->get_type()));
            return true;
        });
}

void definition_cache::add_core(name const & n, expr const & pre_type, expr const & pre_value,
                                level_param_names const & ls, expr const & type, expr const & value,
                                dependencies const & deps, uint64 fingerprint) {
    m_definitions.insert(n, entry(pre_type, pre_value, ls, type, value, deps, fingerprint));
}

void definition_cache::add(environment const & env, name const & n, expr const & pre_type, expr const & pre_value,
                           level_param_names const & ls, expr const & type, expr const & value) {
    dependencies deps;
    collect_dependencies(env, type, deps);
    collect_dependencies(env, value, deps);
    uint64 fingerprint = get_fingerprint(env);
    lock_guard<mutex> lc(m_mutex);
    add_core(n, pre_type, pre_value, ls, type, value, deps, fingerprint);
}

void definition_cache::erase(name const & n) {
    lock_guard<mutex> lc(m_mutex);
    m_definitions.erase(n);
}

void definition_cache::clear() {
    lock_guard<mutex> lc(m_mutex);
    m_definitions.clear();
}

/** \brief Return true iff the type of all declarations in deps still have the same hashcode
    stored in deps. */
bool definition_cache::check_dependencies(environment const & env, dependencies const & deps) {
    bool ok = true;
    deps.for_each([&](name const & n, unsigned h) {
            if (ok) {
                if (auto d = env.find(n)) {
                    if (h != hash_bi(d->get_type()))
                        ok = false;
                } else {
                    ok = false;
                }
            }
        });
    return ok;
}

optional<std::tuple<level_param_names, expr, expr>>
definition_cache::find(environment const & env, name const & n, expr const & pre_type, expr const & pre_value) {
    entry e;
    {
        lock_guard<mutex> lc(m_mutex);
        if (auto it = m_definitions.find(n)) {
            e = *it;
        } else {
            return optional<std::tuple<level_param_names, expr, expr>>();
        }
    }
    level_param_names ls;
    if (expr_eq_modulo_placeholders_fn()(e.m_pre_type, pre_type) &&
        expr_eq_modulo_placeholders_fn()(e.m_pre_value, pre_value) &&
        get_fingerprint(env) == e.m_fingerprint &&
        check_dependencies(env, e.m_dependencies)) {
        return some(std::make_tuple(e.m_params, e.m_type, e.m_value));
    } else {
        return optional<std::tuple<level_param_names, expr, expr>>();
    }
}

void definition_cache::save(std::ostream & out) {
    lock_guard<mutex> lc(m_mutex);
    serializer s(out);
    s << m_definitions.size();
    m_definitions.for_each([&](name const & n, entry const & e) {
            s << n << e.m_pre_type << e.m_pre_value << e.m_params
              << e.m_type << e.m_value;
            s << static_cast<unsigned>(e.m_dependencies.size());
            e.m_dependencies.for_each([&](name const & n, unsigned h) {
                    s << n << h;
                });
            s << e.m_fingerprint;
        });
}
}
