/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include "kernel/replace_fn.h"
#include "kernel/cache_stack.h"

#ifndef LEAN_DEFAULT_REPLACE_CACHE_CAPACITY
#define LEAN_DEFAULT_REPLACE_CACHE_CAPACITY 1024*8
#endif

#ifndef LEAN_REPLACE_SMALL_TERM_THRESHOLD
#define LEAN_REPLACE_SMALL_TERM_THRESHOLD 10000
#endif

namespace lean {
struct replace_cache {
    struct entry {
        expr_cell * m_cell;
        unsigned    m_offset;
        expr        m_result;
        entry():m_cell(nullptr) {}
    };
    unsigned              m_capacity;
    std::vector<entry>    m_cache;
    std::vector<unsigned> m_used;
    replace_cache(unsigned c):m_capacity(c), m_cache(c) {}

    expr * find(expr const & e, unsigned offset) {
        unsigned i = hash(e.hash_alloc(), offset) % m_capacity;
        if (m_cache[i].m_cell == e.raw() && m_cache[i].m_offset == offset)
            return &m_cache[i].m_result;
        else
            return nullptr;
    }

    void insert(expr const & e, unsigned offset, expr const & v) {
        unsigned i = hash(e.hash_alloc(), offset) % m_capacity;
        if (m_cache[i].m_cell == nullptr)
            m_used.push_back(i);
        m_cache[i].m_cell   = e.raw();
        m_cache[i].m_offset = offset;
        m_cache[i].m_result = v;
    }

    void clear() {
        for (unsigned i : m_used) {
            m_cache[i].m_cell   = nullptr;
            m_cache[i].m_result = expr();
        }
        m_used.clear();
    }
};

MK_CACHE_STACK(replace_cache, LEAN_DEFAULT_REPLACE_CACHE_CAPACITY)

class replace_rec_fn {
    replace_cache_ref                                     m_cache;
    std::function<optional<expr>(expr const &, unsigned)> m_f;
    bool                                                  m_use_cache;

    expr save_result(expr const & e, unsigned offset, expr const & r, bool shared) {
        if (shared)
            m_cache->insert(e, offset, r);
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        bool shared = false;
        if (m_use_cache && is_shared(e)) {
            if (auto r = m_cache->find(e, offset))
                return *r;
            shared = true;
        }
        check_interrupted();
        check_memory("replace");

        if (optional<expr> r = m_f(e, offset)) {
            return save_result(e, offset, *r, shared);
        } else {
            switch (e.kind()) {
            case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Var:
                return save_result(e, offset, e, shared);
            case expr_kind::Meta:     case expr_kind::Local: {
                expr new_t = apply(mlocal_type(e), offset);
                return save_result(e, offset, update_mlocal(e, new_t), shared);
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
            case expr_kind::Macro: {
                buffer<expr> new_args;
                unsigned nargs = macro_num_args(e);
                for (unsigned i = 0; i < nargs; i++)
                    new_args.push_back(apply(macro_arg(e, i), offset));
                return save_result(e, offset, update_macro(e, new_args.size(), new_args.data()), shared);
            }}
            lean_unreachable();
        }
    }
public:
    template<typename F>
    replace_rec_fn(F const & f, bool use_cache):m_f(f), m_use_cache(use_cache) {}

    expr operator()(expr const & e) { return apply(e, 0); }
};

expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache) {
    return replace_rec_fn(f, use_cache)(e);
}
}
