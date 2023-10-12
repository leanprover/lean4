/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include "runtime/interrupt.h"
#include "runtime/thread.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"

#ifndef LEAN_EQ_CACHE_CAPACITY
#define LEAN_EQ_CACHE_CAPACITY 1024*8
#endif

namespace lean {
struct eq_cache {
    struct entry {
        object * m_a;
        object * m_b;
        entry():m_a(nullptr), m_b(nullptr) {}
    };
    unsigned              m_capacity;
    std::vector<entry>    m_cache;
    std::vector<unsigned> m_used;
    eq_cache():m_capacity(LEAN_EQ_CACHE_CAPACITY), m_cache(LEAN_EQ_CACHE_CAPACITY) {}

    bool check(expr const & a, expr const & b) {
        if (!is_shared(a) || !is_shared(b))
            return false;
        unsigned i = hash(hash(a), hash(b)) % m_capacity;
        if (m_cache[i].m_a == a.raw() && m_cache[i].m_b == b.raw()) {
            return true;
        } else {
            if (m_cache[i].m_a == nullptr)
                m_used.push_back(i);
            m_cache[i].m_a = a.raw();
            m_cache[i].m_b = b.raw();
            return false;
        }
    }

    void clear() {
        for (unsigned i : m_used)
            m_cache[i].m_a = nullptr;
        m_used.clear();
    }
};

/* CACHE_RESET: No */
MK_THREAD_LOCAL_GET_DEF(eq_cache, get_eq_cache);

/** \brief Functional object for comparing expressions.

    Remark if CompareBinderInfo is true, then functional object will also compare
    binder information attached to lambda and Pi expressions */
template<bool CompareBinderInfo>
class expr_eq_fn {
    eq_cache & m_cache;

    static void check_system() {
        ::lean::check_system("expression equality test");
    }

    bool apply(expr const & a, expr const & b) {
        if (is_eqp(a, b))          return true;
        if (hash(a) != hash(b))    return false;
        if (a.kind() != b.kind())  return false;
        if (is_bvar(a))            return bvar_idx(a) == bvar_idx(b);
        if (m_cache.check(a, b))
            return true;
        /*
           We increase the number of heartbeats here because some code (e.g., `simp`) may spend a lot of time comparing
           `Expr`s (e.g., checking a cache with many collisions) without allocating any significant amount of memory.
         */
        lean_inc_heartbeat();
        switch (a.kind()) {
        case expr_kind::BVar:
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
        case expr_kind::Lit:
            return lit_value(a) == lit_value(b);
        case expr_kind::Const:
            return
                const_name(a) == const_name(b) &&
                compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2) { return l1 == l2; });
        case expr_kind::MVar:
            return mvar_name(a) == mvar_name(b);
        case expr_kind::FVar:
            return fvar_name(a) == fvar_name(b);
        case expr_kind::App:
            check_system();
            return
                apply(app_fn(a), app_fn(b)) &&
                apply(app_arg(a), app_arg(b));
        case expr_kind::Lambda: case expr_kind::Pi:
            check_system();
            return
                apply(binding_domain(a), binding_domain(b)) &&
                apply(binding_body(a), binding_body(b)) &&
                (!CompareBinderInfo || binding_name(a) == binding_name(b)) &&
                (!CompareBinderInfo || binding_info(a) == binding_info(b));
        case expr_kind::Let:
            check_system();
            return
                apply(let_type(a), let_type(b)) &&
                apply(let_value(a), let_value(b)) &&
                apply(let_body(a), let_body(b)) &&
                (!CompareBinderInfo || let_name(a) == let_name(b));
        case expr_kind::Sort:
            return sort_level(a) == sort_level(b);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
public:
    expr_eq_fn():m_cache(get_eq_cache()) {}
    ~expr_eq_fn() { m_cache.clear(); }
    bool operator()(expr const & a, expr const & b) { return apply(a, b); }
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
