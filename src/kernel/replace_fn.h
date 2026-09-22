/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <tuple>
#include <utility>
#include "runtime/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "util/alloc.h"

namespace lean {

// Small-buffer cache for `replace_rec_fn`. The histogram of cache sizes during
// a typical run is heavily skewed toward small caches: ~87% of instances hold
// ≤15 entries and ~99% hold ≤63, with a long thin tail up to a few thousand.
// A linear scan over a stack-resident array beats any hash map at that scale,
// so we keep the first `INLINE_CAP` entries inline and only fall back to a
// real hash map (lazily allocated) for the rare large traversal.
class replace_cache {
    struct key_hasher {
        std::size_t operator()(std::pair<lean_object *, unsigned> const & p) const {
            return hash((size_t)p.first >> 3, p.second);
        }
    };
    using key_t = std::pair<lean_object *, unsigned>;
    using map_t = lean::unordered_map<key_t, expr, key_hasher>;
    static constexpr unsigned INLINE_CAP = 16;
    struct entry { key_t k; expr v; };
    // Uninitialized storage; only entries [0, m_size) are constructed. This
    // avoids paying for `INLINE_CAP` default-constructed `expr`s on every
    // `replace_rec_fn` instance, which matters because the typical traversal
    // creates a fresh cache holding only a handful of entries.
    alignas(entry) std::byte m_inline_storage[sizeof(entry) * INLINE_CAP];
    unsigned m_size = 0;
    std::unique_ptr<map_t> m_overflow;

    entry * inline_at(unsigned i) {
        return std::launder(reinterpret_cast<entry *>(m_inline_storage) + i);
    }
    entry const * inline_at(unsigned i) const {
        return std::launder(reinterpret_cast<entry const *>(m_inline_storage) + i);
    }
public:
    replace_cache() = default;
    replace_cache(replace_cache const &) = delete;
    replace_cache & operator=(replace_cache const &) = delete;
    ~replace_cache() {
        for (unsigned i = 0; i < m_size; ++i) inline_at(i)->~entry();
    }

    expr const * find(key_t const & k) const {
        for (unsigned i = 0; i < m_size; ++i) {
            entry const * e = inline_at(i);
            if (e->k == k) return &e->v;
        }
        if (m_overflow) {
            auto it = m_overflow->find(k);
            if (it != m_overflow->end()) return &it->second;
        }
        return nullptr;
    }
    void insert(key_t const & k, expr const & v) {
        if (!m_overflow) {
            if (m_size < INLINE_CAP) {
                new (inline_at(m_size)) entry{k, v};
                ++m_size;
                return;
            }
            // Promote: drain inline entries into the overflow map and reset
            // `m_size` so future finds skip the (now-empty) inline scan and
            // future inserts go straight to overflow. Without this drain,
            // workloads with a long tail of large caches (e.g. the `big_do`
            // elab benchmark, where ~3% of caches hold 1k-8k entries but
            // contribute essentially all the lookup work) waste 16 stale
            // comparisons on every post-promotion lookup.
            m_overflow.reset(new map_t());
            m_overflow->reserve(INLINE_CAP * 4);
            for (unsigned i = 0; i < m_size; ++i) {
                entry * e = inline_at(i);
                m_overflow->emplace(e->k, std::move(e->v));
                e->~entry();
            }
            m_size = 0;
        }
        m_overflow->insert(mk_pair(k, v));
    }
};

/// Default skip predicate: never skips. Used by `replace_rec_fn` callers that
/// don't want a pre-cache bail-out.
struct replace_no_skip {
    bool operator()(expr const &, unsigned) const { return false; }
};

/**
   \brief Class-template implementation of `replace`. Stores the user functor by
   value (not via `std::function`) so calls into it inline at every recursion
   step. Hot callers should instantiate this directly via `replace<F>(...)`;
   the legacy `std::function`-typed `replace` overload below is a thin wrapper
   for cold/external callers that need type erasure.

   The functor `F` must be callable as `F(expr const &, unsigned) -> optional<expr>`.
   The optional `Skip` predicate is invoked *before* the cache lookup; if it
   returns true the input is returned unchanged with no cache touch. Use this
   for cheap "this entire subtree is unaffected" guards (e.g. a memoized
   loose-bvar-range check) — it both avoids the cache lookup and avoids
   polluting the cache with identity entries, without the pitfall of an
   `r == e` check in `save_result` that would also drop the *recursion-identity*
   case and blow up exponentially on workloads like `Init.WFExtrinsicFix`.
*/
template<typename F, typename Skip = replace_no_skip>
class replace_rec_fn {
    replace_cache m_cache;
    Skip m_skip;
    F    m_f;
    bool m_use_cache;

    expr save_result(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared)
            m_cache.insert(mk_pair(e.raw(), offset), r);
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        if (m_skip(e, offset))
            return e;
        bool shared = false;
        if (m_use_cache && !is_likely_unshared(e)) {
            if (expr const * cached = m_cache.find(mk_pair(e.raw(), offset)))
                return *cached;
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
    template<typename G>
    replace_rec_fn(G && f, bool use_cache):m_f(std::forward<G>(f)), m_use_cache(use_cache) {}
    template<typename H, typename G>
    replace_rec_fn(H && skip, G && f, bool use_cache):
        m_skip(std::forward<H>(skip)), m_f(std::forward<G>(f)), m_use_cache(use_cache) {}

    expr operator()(expr const & e) { return apply(e, 0); }
};

/**
   \brief Apply <tt>f</tt> to the subexpressions of a given expression.

   f is invoked for each subexpression \c s of the input expression e.
   In a call <tt>f(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if f return none_expr.

   These templated overloads monomorphize on the functor type so the call into
   `f` inlines at every recursion step. Prefer them over the `std::function`
   overloads for hot callers. The first overload accepts functors taking
   `(expr const &, unsigned)`; the second accepts functors taking just
   `(expr const &)` and adapts them by ignoring the offset argument.
*/
template<typename F, std::enable_if_t<std::is_invocable_v<F const &, expr const &, unsigned>, int> = 0>
inline expr replace(expr const & e, F && f, bool use_cache = true) {
    return replace_rec_fn<std::decay_t<F>>(std::forward<F>(f), use_cache)(e);
}

template<typename F, std::enable_if_t<std::is_invocable_v<F const &, expr const &> &&
                                      !std::is_invocable_v<F const &, expr const &, unsigned>, int> = 0>
inline expr replace(expr const & e, F && f, bool use_cache = true) {
    auto adapter = [f = std::forward<F>(f)](expr const & e, unsigned) { return f(e); };
    return replace_rec_fn<decltype(adapter)>(std::move(adapter), use_cache)(e);
}

/**
   \brief As the templated `replace` above, but with a pre-cache `skip`
   predicate. `skip(m, offset)` is invoked before any cache lookup; if it
   returns true, `m` is returned unchanged with no cache touch.
*/
template<typename Skip, typename F,
         std::enable_if_t<std::is_invocable_r_v<bool, Skip const &, expr const &, unsigned> &&
                          std::is_invocable_v<F const &, expr const &, unsigned>, int> = 0>
inline expr replace(expr const & e, Skip && skip, F && f, bool use_cache = true) {
    return replace_rec_fn<std::decay_t<F>, std::decay_t<Skip>>(
        std::forward<Skip>(skip), std::forward<F>(f), use_cache)(e);
}

/**
   \brief Type-erased overload of `replace` for cold callers and external use.
   Internally instantiates `replace_rec_fn<std::function<...>>`, so it pays the
   `std::function` indirection on every recursive call.
*/
expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache = true);
inline expr replace(expr const & e, std::function<optional<expr>(expr const &)> const & f, bool use_cache = true) {
    return replace(e, [&](expr const & e, unsigned) { return f(e); }, use_cache);
}

/**
   \brief As `replace`, but with a pre-cache skip predicate. `skip(m, offset)`
   is called before any cache lookup; if it returns true, `m` is returned
   unchanged with no cache touch. Use this for cheap "this entire subtree is
   unaffected" guards (e.g. a memoized loose-bvar-range check), since it both
   skips the cache lookup and avoids polluting the cache with identity entries.
*/
expr replace(expr const & e,
             std::function<bool(expr const &, unsigned)> const & skip,
             std::function<optional<expr>(expr const &, unsigned)> const & f,
             bool use_cache = true);
}
