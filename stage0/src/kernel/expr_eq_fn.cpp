/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include "runtime/alloc.h"
#include "runtime/interrupt.h"
#include "runtime/thread.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "kernel/ptr_pair_set.h"
#include "util/alloc.h"

namespace lean {
/**
\brief Functional object for comparing expressions.

Remark if CompareBinderInfo is true, then functional object will also compare
binder information attached to lambda and Pi expressions
*/
template<bool CompareBinderInfo>
class expr_eq_fn {
    ptr_pair_set m_cache;
    size_t m_counter = 0;
    bool check_cache(expr const & a, expr const & b) {
        if (!is_shared(a) || !is_shared(b))
            return false;
        return !m_cache.insert(a.raw(), reinterpret_cast<uintptr_t>(b.raw()));
    }
    bool apply(expr const & a, expr const & b, bool root = false) {
        if (is_eqp(a, b))          return true;
        if (hash(a) != hash(b))    return false;
        if (a.kind() != b.kind())  return false;
        switch (a.kind()) {
        case expr_kind::BVar: return bvar_idx(a) == bvar_idx(b);
        case expr_kind::Lit:  return lit_value(a) == lit_value(b);
        case expr_kind::MVar: return mvar_name(a) == mvar_name(b);
        case expr_kind::FVar: return fvar_name(a) == fvar_name(b);
        case expr_kind::Sort: return sort_level(a) == sort_level(b);
        default: break;
        }
        if (!root && check_cache(a, b)) {
            return true;
        }
        /*
           We increase the number of heartbeats here because some code (e.g., `simp`) may spend a lot of time comparing
           `Expr`s (e.g., checking a cache with many collisions) without allocating any significant amount of memory.
           We use the counter to invoke `add_heartbeats` later. Reason: heartbeat is a thread local storage, and morexpensive to update.
         */
        m_counter++;
        switch (a.kind()) {
        case expr_kind::BVar:
        case expr_kind::Lit:
        case expr_kind::MVar:
        case expr_kind::FVar:
        case expr_kind::Sort:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::MData:
            return
                apply(mdata_expr(a), mdata_expr(b)) &&
                mdata_data(a) == mdata_data(b);
        case expr_kind::Proj:
            return
                apply(proj_expr(a), proj_expr(b)) &&
                proj_sname(a) == proj_sname(b) &&
                proj_idx(a) == proj_idx(b);
        case expr_kind::Const:
            return
                const_name(a) == const_name(b) &&
                compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2) { return l1 == l2; });
        case expr_kind::App: {
            if (!apply(app_arg(a), app_arg(b))) return false;
            expr const * curr_a = &app_fn(a);
            expr const * curr_b = &app_fn(b);
            while (true) {
                if (!is_app(*curr_a)) break;
                if (!is_app(*curr_b)) return false;
                if (!apply(app_arg(*curr_a), app_arg(*curr_b))) return false;
                curr_a = &app_fn(*curr_a);
                curr_b = &app_fn(*curr_b);
            }
            return apply(*curr_a, *curr_b);
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            return
                apply(binding_domain(a), binding_domain(b)) &&
                apply(binding_body(a), binding_body(b)) &&
                (!CompareBinderInfo || binding_name(a) == binding_name(b)) &&
                (!CompareBinderInfo || binding_info(a) == binding_info(b));
        case expr_kind::Let:
            return
                apply(let_type(a), let_type(b)) &&
                apply(let_value(a), let_value(b)) &&
                apply(let_body(a), let_body(b)) &&
                let_nondep(a) == let_nondep(b) &&
                (!CompareBinderInfo || let_name(a) == let_name(b));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
public:
    expr_eq_fn() {}
    ~expr_eq_fn() {
        if (m_counter > 0) add_heartbeats(m_counter);
    }
    bool operator()(expr const & a, expr const & b) { return apply(a, b, true); }
};

bool is_equal(expr const & a, expr const & b) {
    return expr_eq_fn<false>()(a, b);
}

extern "C" LEAN_EXPORT uint8 lean_expr_eqv(b_obj_arg a, b_obj_arg b) {
    return expr_eq_fn<false>()(TO_REF(expr, a), TO_REF(expr, b));
}

extern "C" LEAN_EXPORT uint8 lean_expr_equal(b_obj_arg a, b_obj_arg b) {
    return expr_eq_fn<true>()(TO_REF(expr, a), TO_REF(expr, b));
}

// Constructor indices of Lean.LBool.
enum class budgeted_eq_result : uint8 { False, True, Exhausted };

/**
   Budgeted equality breaks referential transparency: pointer sharing can determine whether a
   comparison finishes within the budget. Exhaustion must be handled as an inconclusive result.
*/
template<bool CompareBinderInfo>
class budgeted_expr_eq_fn {
    ptr_pair_set m_cache;
    size_t const m_initial_budget;
    size_t m_remaining;
    bool m_exhausted = false;

    bool check_cache(expr const & a, expr const & b) {
        if (!is_shared(a) || !is_shared(b))
            return false;
        return !m_cache.insert(a.raw(), reinterpret_cast<uintptr_t>(b.raw()));
    }

    bool consume(size_t n = 1) {
        if (n > m_remaining) {
            m_exhausted = true;
            return false;
        }
        m_remaining -= n;
        return true;
    }

    bool charge_payload(object * o) {
        if (is_scalar(o)) return true;
        if (is_cnstr(o)) {
            unsigned n = cnstr_num_objs(o);
            if (!consume(n)) return false;
            for (unsigned i = 0; i < n; i++)
                if (!charge_payload(cnstr_get(o, i))) return false;
        } else if (is_array(o)) {
            size_t n = array_size(o);
            if (!consume(n)) return false;
            for (size_t i = 0; i < n; i++)
                if (!charge_payload(array_cptr(o)[i])) return false;
        } else if (is_string(o)) {
            return consume(string_size(o));
        } else if (is_mpz(o)) {
            return consume(mpz_value(o).size_in_bytes());
        } else {
            m_exhausted = true;
            return false;
        }
        return true;
    }

    bool string_eq(string_ref const & s1, string_ref const & s2) {
        if (s1.raw() == s2.raw()) return true;
        size_t n = s1.num_bytes();
        if (n != s2.num_bytes()) return false;
        return consume(n) && s1 == s2;
    }

    bool data_value_eq(data_value const & a, data_value const & b) {
        if (a.raw() == b.raw()) return true;
        if (a.kind() != b.kind()) return false;
        switch (a.kind()) {
        case data_value_kind::String:
            return string_eq(a.get_string(), b.get_string());
        case data_value_kind::Syntax:
            // Syntax.structEq revisits shared nodes; bound it by both unfolded trees.
            return charge_payload(a.raw()) && charge_payload(b.raw()) && a == b;
        default:
            return a == b;
        }
    }

    bool mdata_eq(kvmap const & a, kvmap const & b) {
        object * it1 = a.raw();
        object * it2 = b.raw();
        while (!is_scalar(it1) && !is_scalar(it2)) {
            if (it1 == it2) return true;
            if (!consume()) return false;
            kvmap_entry const & e1 = head<kvmap_entry>(it1);
            kvmap_entry const & e2 = head<kvmap_entry>(it2);
            if (e1.fst() != e2.fst() || !data_value_eq(e1.snd(), e2.snd())) return false;
            it1 = cnstr_get(it1, 1);
            it2 = cnstr_get(it2, 1);
        }
        return is_scalar(it1) && is_scalar(it2);
    }

    bool literal_eq(literal const & a, literal const & b) {
        if (a.kind() != b.kind()) return false;
        switch (a.kind()) {
        case literal_kind::Nat:
            return a.get_nat() == b.get_nat();
        case literal_kind::String:
            return string_eq(a.get_string(), b.get_string());
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    bool apply(expr const & a, expr const & b, bool root = false) {
        if (is_eqp(a, b))          return true;
        if (hash(a) != hash(b))    return false;
        if (a.kind() != b.kind())  return false;
        switch (a.kind()) {
        case expr_kind::BVar: return bvar_idx(a) == bvar_idx(b);
        case expr_kind::Lit:  return literal_eq(lit_value(a), lit_value(b));
        case expr_kind::MVar: return mvar_name(a) == mvar_name(b);
        case expr_kind::FVar: return fvar_name(a) == fvar_name(b);
        case expr_kind::Sort: return sort_level(a) == sort_level(b);
        default: break;
        }
        if (!root && check_cache(a, b)) {
            return true;
        }
        if (!consume()) return false;
        switch (a.kind()) {
        case expr_kind::BVar:
        case expr_kind::Lit:
        case expr_kind::MVar:
        case expr_kind::FVar:
        case expr_kind::Sort:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::MData:
            return
                apply(mdata_expr(a), mdata_expr(b)) &&
                mdata_eq(mdata_data(a), mdata_data(b));
        case expr_kind::Proj:
            return
                apply(proj_expr(a), proj_expr(b)) &&
                proj_sname(a) == proj_sname(b) &&
                proj_idx(a) == proj_idx(b);
        case expr_kind::Const:
            return
                const_name(a) == const_name(b) &&
                compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2) { return l1 == l2; });
        case expr_kind::App: {
            if (!apply(app_arg(a), app_arg(b))) return false;
            expr const * curr_a = &app_fn(a);
            expr const * curr_b = &app_fn(b);
            while (true) {
                if (!is_app(*curr_a)) break;
                if (!is_app(*curr_b)) return false;
                if (!consume()) return false;
                if (!apply(app_arg(*curr_a), app_arg(*curr_b))) return false;
                curr_a = &app_fn(*curr_a);
                curr_b = &app_fn(*curr_b);
            }
            return apply(*curr_a, *curr_b);
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            return
                apply(binding_domain(a), binding_domain(b)) &&
                apply(binding_body(a), binding_body(b)) &&
                (!CompareBinderInfo || binding_name(a) == binding_name(b)) &&
                (!CompareBinderInfo || binding_info(a) == binding_info(b));
        case expr_kind::Let:
            return
                apply(let_type(a), let_type(b)) &&
                apply(let_value(a), let_value(b)) &&
                apply(let_body(a), let_body(b)) &&
                let_nondep(a) == let_nondep(b) &&
                (!CompareBinderInfo || let_name(a) == let_name(b));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

public:
    explicit budgeted_expr_eq_fn(size_t budget):m_initial_budget(budget), m_remaining(budget) {}
    ~budgeted_expr_eq_fn() {
        size_t consumed = m_initial_budget - m_remaining;
        if (consumed > 0) add_heartbeats(consumed);
    }
    budgeted_eq_result operator()(expr const & a, expr const & b) {
        if (apply(a, b, true)) return budgeted_eq_result::True;
        return m_exhausted ? budgeted_eq_result::Exhausted : budgeted_eq_result::False;
    }
};

extern "C" LEAN_EXPORT uint8 lean_expr_eqv_budgeted(b_obj_arg a, b_obj_arg b, size_t budget) {
    return static_cast<uint8>(budgeted_expr_eq_fn<false>(budget)(TO_REF(expr, a), TO_REF(expr, b)));
}

extern "C" LEAN_EXPORT uint8 lean_expr_equal_budgeted(b_obj_arg a, b_obj_arg b, size_t budget) {
    return static_cast<uint8>(budgeted_expr_eq_fn<true>(budget)(TO_REF(expr, a), TO_REF(expr, b)));
}
}
