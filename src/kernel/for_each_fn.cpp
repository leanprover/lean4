/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <unordered_map>
#include <utility>
#include "runtime/memory.h"
#include "runtime/interrupt.h"
#include "runtime/flet.h"
#include "kernel/for_each_fn.h"

namespace lean {

/*
If `partial_apps = true`, then given a term `g a b`, we also apply the function `m_f` to `g a`,
and not only to `g`, `a`, and `b`.
*/
template<bool partial_apps> class for_each_fn {
    std::unordered_set<lean_object *> m_cache;
    std::function<bool(expr const &)> m_f; // NOLINT

    bool visited(expr const & e) {
        if (!is_shared(e)) return false;
        if (m_cache.find(e.raw()) != m_cache.end()) return true;
        m_cache.insert(e.raw());
        return false;
    }

    void apply_fn(expr const & e) {
        if (is_app(e)) {
            apply_fn(app_fn(e));
            apply(app_arg(e));
        } else {
            apply(e);
        }
    }

    void apply(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar: case expr_kind::Sort:
            m_f(e);
            return;
        default:
            break;
        }

        if (visited(e))
            return;

        if (!m_f(e))
            return;

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar:
        case expr_kind::Sort:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return;
        case expr_kind::MData:
            apply(mdata_expr(e));
            return;
        case expr_kind::Proj:
            apply(proj_expr(e));
            return;
        case expr_kind::App:
            if (partial_apps)
                apply(app_fn(e));
            else
                apply_fn(app_fn(e));
            apply(app_arg(e));
            return;
        case expr_kind::Lambda: case expr_kind::Pi:
            apply(binding_domain(e));
            apply(binding_body(e));
            return;
        case expr_kind::Let:
            apply(let_type(e));
            apply(let_value(e));
            apply(let_body(e));
            return;
        }
    }

public:
    for_each_fn(std::function<bool(expr const &)> && f):m_f(f) {}        // NOLINT
    for_each_fn(std::function<bool(expr const &)> const & f):m_f(f) {}   // NOLINT
    void operator()(expr const & e) { apply(e); }
};

class for_each_offset_fn {
    struct key_hasher {
        std::size_t operator()(std::pair<lean_object *, unsigned> const & p) const {
            return hash((size_t)p.first, p.second);
        }
    };
    std::unordered_set<std::pair<lean_object *, unsigned>, key_hasher> m_cache;
    std::function<bool(expr const &, unsigned)> m_f; // NOLINT

    bool visited(expr const & e, unsigned offset) {
        if (!is_shared(e)) return false;
        if (m_cache.find(std::make_pair(e.raw(), offset)) != m_cache.end()) return true;
        m_cache.insert(std::make_pair(e.raw(), offset));
        return false;
    }

    void apply(expr const & e, unsigned offset) {
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar: case expr_kind::Sort:
            m_f(e, offset);
            return;
        default:
            break;
        }

        if (visited(e, offset))
            return;

        if (!m_f(e, offset))
            return;

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar:
        case expr_kind::Sort:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return;
        case expr_kind::MData:
            apply(mdata_expr(e), offset);
            return;
        case expr_kind::Proj:
            apply(proj_expr(e), offset);
            return;
        case expr_kind::App:
            apply(app_fn(e), offset);
            apply(app_arg(e), offset);
            return;
        case expr_kind::Lambda: case expr_kind::Pi:
            apply(binding_domain(e), offset);
            apply(binding_body(e), offset+1);
            return;
        case expr_kind::Let:
            apply(let_type(e), offset);
            apply(let_value(e), offset);
            apply(let_body(e), offset+1);
            return;
        }
    }

public:
    for_each_offset_fn(std::function<bool(expr const &, unsigned)> && f):m_f(f) {}        // NOLINT
    for_each_offset_fn(std::function<bool(expr const &, unsigned)> const & f):m_f(f) {}   // NOLINT
    void operator()(expr const & e) { apply(e, 0); }
};

void for_each(expr const & e, std::function<bool(expr const &)> && f) { // NOLINT
    return for_each_fn<true>(f)(e);
}

void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f) { // NOLINT
    return for_each_offset_fn(f)(e);
}

extern "C" LEAN_EXPORT obj_res lean_find_expr(b_obj_arg p, b_obj_arg e_) {
    lean_object * found = nullptr;
    expr const & e = TO_REF(expr, e_);
    for_each_fn<true>([&](expr const & e) {
        if (found != nullptr) return false;
        lean_inc(p);
        lean_inc(e.raw());
        if (lean_unbox(lean_apply_1(p, e.raw()))) {
            found = e.raw();
            return false;
        }
        return true;
    })(e);
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}

/*
Similar to `lean_find_expr`, but `p` returns
```
inductive FindStep where
  /-- Found desired subterm -/ | found
  /-- Search subterms -/ | visit
  /-- Do not search subterms -/ | done
```
*/
extern "C" LEAN_EXPORT obj_res lean_find_ext_expr(b_obj_arg p, b_obj_arg e_) {
    lean_object * found = nullptr;
    expr const & e = TO_REF(expr, e_);
    // Recall that `findExt?` skips partial applications.
    for_each_fn<false>([&](expr const & e) {
        if (found != nullptr) return false;
        lean_inc(p);
        lean_inc(e.raw());
        switch(lean_unbox(lean_apply_1(p, e.raw()))) {
        case 0: // found
            found = e.raw();
            return false;
        case 1: // visit
            return true;
        case 2: // done
            return false;
        default:
            lean_unreachable();
        }
    })(e);
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}
}
