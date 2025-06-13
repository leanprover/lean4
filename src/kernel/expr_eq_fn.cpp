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

namespace lean {
/**
\brief Functional object for comparing expressions.

Remark if CompareBinderInfo is true, then functional object will also compare
binder information attached to lambda and Pi expressions
*/
template<bool CompareBinderInfo>
class expr_eq_fn {
    struct key_hasher {
        std::size_t operator()(std::pair<lean_object *, lean_object *> const & p) const {
            return hash((size_t)p.first >> 3, (size_t)p.second >> 3);
        }
    };
    typedef std::unordered_set<std::pair<lean_object *, lean_object *>, key_hasher> cache;
    cache * m_cache = nullptr;
    size_t m_max_stack_depth = 0;
    size_t m_counter = 0;
    bool check_cache(expr const & a, expr const & b) {
        if (!is_shared(a) || !is_shared(b))
            return false;
        if (!m_cache)
            m_cache = new cache();
        std::pair<lean_object *, lean_object *> key(a.raw(), b.raw());
        if (m_cache->find(key) != m_cache->end())
            return true;
        m_cache->insert(key);
        return false;
    }
    void check_system(unsigned depth) {
        /*
        We used to use `lean::check_system` here. We claim it is ok to not check memory consumption here.
        Note that `do_check_interrupted` was set to `false`. Thus, `check_interrupted` and `check_heartbeat` were not being used.
        */
        if (depth > m_max_stack_depth) {
            if (m_max_stack_depth > 0)
                throw stack_space_exception("expression equality test");
        }
    }
    bool apply(expr const & a, expr const & b, unsigned depth, bool root = false) {
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
        if (root) {
            m_max_stack_depth = get_available_stack_size() / 256;
        } else if (check_cache(a, b)) {
            return true;
        }
        /*
           We increase the number of heartbeats here because some code (e.g., `simp`) may spend a lot of time comparing
           `Expr`s (e.g., checking a cache with many collisions) without allocating any significant amount of memory.
           We use the counter to invoke `add_heartbeats` later. Reason: heartbeat is a thread local storage, and morexpensive to update.
         */
        m_counter++;
        depth++;
        switch (a.kind()) {
        case expr_kind::BVar:
        case expr_kind::Lit:
        case expr_kind::MVar:
        case expr_kind::FVar:
        case expr_kind::Sort:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::MData:
            return
                apply(mdata_expr(a), mdata_expr(b), depth) &&
                mdata_data(a) == mdata_data(b);
        case expr_kind::Proj:
            return
                apply(proj_expr(a), proj_expr(b), depth) &&
                proj_sname(a) == proj_sname(b) &&
                proj_idx(a) == proj_idx(b);
        case expr_kind::Const:
            return
                const_name(a) == const_name(b) &&
                compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2) { return l1 == l2; });
        case expr_kind::App: {
            check_system(depth);
            if (!apply(app_arg(a), app_arg(b), depth)) return false;
            expr const * curr_a = &app_fn(a);
            expr const * curr_b = &app_fn(b);
            while (true) {
                if (!is_app(*curr_a)) break;
                if (!is_app(*curr_b)) return false;
                if (!apply(app_arg(*curr_a), app_arg(*curr_b), depth)) return false;
                curr_a = &app_fn(*curr_a);
                curr_b = &app_fn(*curr_b);
            }
            return apply(*curr_a, *curr_b, depth);
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            check_system(depth);
            return
                apply(binding_domain(a), binding_domain(b), depth) &&
                apply(binding_body(a), binding_body(b), depth) &&
                (!CompareBinderInfo || binding_name(a) == binding_name(b)) &&
                (!CompareBinderInfo || binding_info(a) == binding_info(b));
        case expr_kind::Let:
            check_system(depth);
            return
                apply(let_type(a), let_type(b), depth) &&
                apply(let_value(a), let_value(b), depth) &&
                apply(let_body(a), let_body(b), depth) &&
                let_nondep(a) == let_nondep(b) &&
                (!CompareBinderInfo || let_name(a) == let_name(b));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
public:
    expr_eq_fn() {}
    ~expr_eq_fn() {
        if (m_cache) delete m_cache;
        if (m_counter > 0) add_heartbeats(m_counter);
    }
    bool operator()(expr const & a, expr const & b) { return apply(a, b, 0, true); }
};

bool is_equal(expr const & a, expr const & b) {
    return expr_eq_fn<false>()(a, b);
}
bool is_bi_equal(expr const & a, expr const & b) {
    return expr_eq_fn<true>()(a, b);
}

extern "C" LEAN_EXPORT uint8 lean_expr_eqv(b_obj_arg a, b_obj_arg b) {
    return expr_eq_fn<false>()(TO_REF(expr, a), TO_REF(expr, b));
}

extern "C" LEAN_EXPORT uint8 lean_expr_equal(b_obj_arg a, b_obj_arg b) {
    return expr_eq_fn<true>()(TO_REF(expr, a), TO_REF(expr, b));
}
}
