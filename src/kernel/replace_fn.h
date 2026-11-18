/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdlib>
#include <new>
#include <tuple>
#include "runtime/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "util/alloc.h"

namespace lean {
/* The cache of `replace_rec_fn` and similar traversals: maps a subterm (by address) and an offset to
   its result. Open addressing, as `std::unordered_map` allocates a node per entry. Keys are not
   reference counted: they are subterms of the traversed term. Inserting an existing key keeps the
   old value. */
class replace_cache {
    struct slot {
        lean_object * m_key; // `nullptr` if empty
        unsigned      m_offset;
        lean_object * m_val; // owned
    };
    static constexpr size_t initial_capacity = 16;
    // Most traversals cache only a few subterms, so the first slots need no allocation.
    slot   m_initial[initial_capacity] = {};
    slot * m_slots = m_initial;
    size_t m_mask  = initial_capacity - 1;
    size_t m_size  = 0;

    static size_t hash_of(lean_object * k, unsigned offset) {
        uint64_t h = (reinterpret_cast<uint64_t>(k) >> 3) ^ (static_cast<uint64_t>(offset) * 0x9E3779B97F4A7C15ull);
        h *= 0xBF58476D1CE4E5B9ull;
        return static_cast<size_t>(h ^ (h >> 31));
    }
    void place(lean_object * k, unsigned offset, lean_object * v) {
        size_t i = hash_of(k, offset) & m_mask;
        while (m_slots[i].m_key)
            i = (i + 1) & m_mask;
        m_slots[i] = slot{k, offset, v};
    }
    void grow() {
        slot * old = m_slots;
        size_t old_cap = m_mask + 1;
        size_t cap = 2 * old_cap;
        slot * slots = static_cast<slot *>(std::calloc(cap, sizeof(slot)));
        if (!slots)
            throw std::bad_alloc();
        m_slots = slots;
        m_mask = cap - 1;
        for (size_t i = 0; i < old_cap; i++)
            if (old[i].m_key)
                place(old[i].m_key, old[i].m_offset, old[i].m_val);
        if (old != m_initial)
            std::free(old);
    }
public:
    replace_cache() {}
    replace_cache(replace_cache const &) = delete;
    ~replace_cache() {
        for (size_t i = 0; i <= m_mask; i++)
            if (m_slots[i].m_key)
                lean_dec(m_slots[i].m_val);
        if (m_slots != m_initial)
            std::free(m_slots);
    }
    /* The cached result for `k` at `offset`, or `nullptr`; borrowed. */
    lean_object * find(lean_object * k, unsigned offset = 0) const {
        size_t i = hash_of(k, offset) & m_mask;
        while (lean_object * key = m_slots[i].m_key) {
            if (key == k && m_slots[i].m_offset == offset)
                return m_slots[i].m_val;
            i = (i + 1) & m_mask;
        }
        return nullptr;
    }
    void insert(lean_object * k, unsigned offset, object_ref const & v) {
        if (2 * (m_size + 1) > m_mask + 1)
            grow();
        size_t i = hash_of(k, offset) & m_mask;
        while (lean_object * key = m_slots[i].m_key) {
            if (key == k && m_slots[i].m_offset == offset)
                return;
            i = (i + 1) & m_mask;
        }
        lean_inc(v.raw());
        m_slots[i] = slot{k, offset, v.raw()};
        m_size++;
    }
};

/* The default `skip` of `replace_tpl`: no subterm is skipped. */
struct replace_skip_none {
    bool operator()(expr const &, unsigned) const { return false; }
};

template<typename F, typename S>
class replace_rec_fn {
    replace_cache m_cache;
    F const & m_f;
    S         m_skip;
    bool      m_use_cache;

    expr save_result(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared)
            m_cache.insert(e.raw(), offset, r);
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        if (m_skip(e, offset))
            return e;
        bool shared = false;
        if (m_use_cache && !is_likely_unshared(e)) {
            if (lean_object * r = m_cache.find(e.raw(), offset))
                return expr(r, true);
            shared = true;
        }
        if (optional<expr> r = m_f(e, offset)) {
            return save_result(e, offset, std::move(*r), shared);
        } else {
            switch (e.kind()) {
            case expr_kind::Const: case expr_kind::Sort:
            case expr_kind::BVar:  case expr_kind::Lit:
            case expr_kind::MVar:  case expr_kind::FVar:
                return save_result(e, offset, e, shared);
            case expr_kind::MData: {
                expr new_e = apply(mdata_expr(e), offset);
                return save_result(e, offset, update_mdata(e, new_e), shared);
            }
            case expr_kind::Proj: {
                expr new_e = apply(proj_expr(e), offset);
                return save_result(e, offset, update_proj(e, new_e), shared);
            }
            case expr_kind::App: {
                expr new_f = apply(app_fn(e), offset);
                expr new_a = apply(app_arg(e), offset);
                return save_result(e, offset, update_app(e, new_f, new_a), shared);
            }
            case expr_kind::Pi: case expr_kind::Lambda: {
                expr new_d = apply(binding_domain(e), offset);
                expr new_b = apply(binding_body(e), offset+1);
                return save_result(e, offset, update_binding(e, new_d, new_b), shared);
            }
            case expr_kind::Let: {
                expr new_t = apply(let_type(e), offset);
                expr new_v = apply(let_value(e), offset);
                expr new_b = apply(let_body(e), offset+1);
                return save_result(e, offset, update_let(e, new_t, new_v, new_b), shared);
            }
            }
            lean_unreachable();
        }
    }
public:
    replace_rec_fn(F const & f, S const & skip, bool use_cache):m_f(f), m_skip(skip), m_use_cache(use_cache) {}

    expr operator()(expr const & e) { return apply(e, 0); }
};

/** \brief `replace` for a statically known `f`, avoiding the `std::function` indirection at every visited node.
    `skip(m, offset)` may only hold if `f(m, offset)` is `m` itself; such subterms are returned without
    consulting or filling the cache, which costs more than `f`'s own early exit. */
template<typename F, typename S = replace_skip_none>
expr replace_tpl(expr const & e, F const & f, bool use_cache = true, S const & skip = S()) {
    return replace_rec_fn<F, S>(f, skip, use_cache)(e);
}

/**
   \brief Apply <tt>f</tt> to the subexpressions of a given expression.

   f is invoked for each subexpression \c s of the input expression e.
   In a call <tt>f(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if f return none_expr.
*/
expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache = true);
inline expr replace(expr const & e, std::function<optional<expr>(expr const &)> const & f, bool use_cache = true) {
    return replace(e, [&](expr const & e, unsigned) { return f(e); }, use_cache);
}
}
