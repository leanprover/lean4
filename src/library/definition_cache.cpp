/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "library/placeholder.h"
#include "library/kernel_serializer.h"
#include "library/definition_cache.h"

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
        add_core(n, pre_type, pre_value, ls, type, value);
    }
}

void definition_cache::add_core(name const & n, expr const & pre_type, expr const & pre_value,
                                 level_param_names const & ls, expr const & type, expr const & value) {
    m_definitions.insert(n, entry(pre_type, pre_value, ls, type, value));
}

void definition_cache::add(name const & n, expr const & pre_type, expr const & pre_value,
                            level_param_names const & ls, expr const & type, expr const & value) {
    lock_guard<mutex> lc(m_mutex);
    add_core(n, pre_type, pre_value, ls, type, value);
}

void definition_cache::erase(name const & n) {
    lock_guard<mutex> lc(m_mutex);
    m_definitions.erase(n);
}

void definition_cache::clear() {
    lock_guard<mutex> lc(m_mutex);
    m_definitions.clear();
}

optional<std::tuple<level_param_names, expr, expr>> definition_cache::find(name const & n, expr const & pre_type, expr const & pre_value) {
    entry const * it;
    {
        lock_guard<mutex> lc(m_mutex);
        it = m_definitions.find(n);
    }
    if (it) {
        level_param_names ls;
        expr c_pre_type, c_pre_value, type, value;
        std::tie(c_pre_type, c_pre_value, ls, type, value) = *it;
        if (expr_eq_modulo_placeholders_fn()(c_pre_type, pre_type) &&
            expr_eq_modulo_placeholders_fn()(c_pre_value, pre_value))
            return some(std::make_tuple(ls, type, value));
    }
    return optional<std::tuple<level_param_names, expr, expr>>();
}

void definition_cache::save(std::ostream & out) {
    lock_guard<mutex> lc(m_mutex);
    serializer s(out);
    s << m_definitions.size();
    m_definitions.for_each([&](name const & n, entry const & e) {
            level_param_names ls;
            expr c_pre_type, c_pre_value, type, value;
            std::tie(c_pre_type, c_pre_value, ls, type, value) = e;
            s << n << c_pre_type << c_pre_value << ls << type << value;
        });
}
}
