/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <utility>
#include "util/flet.h"
#include "util/memory.h"
#include "util/interrupt.h"
#include "kernel/for_each_fn.h"
#include "kernel/cache_stack.h"

#ifndef LEAN_DEFAULT_FOR_EACH_CACHE_CAPACITY
#define LEAN_DEFAULT_FOR_EACH_CACHE_CAPACITY 1024*8
#endif

namespace lean {
struct for_each_cache {
    struct entry {
        expr_cell const * m_cell;
        unsigned          m_offset;
        entry():m_cell(nullptr) {}
    };
    unsigned              m_capacity;
    std::vector<entry>    m_cache;
    std::vector<unsigned> m_used;
    for_each_cache(unsigned c):m_capacity(c), m_cache(c) {}

    bool visited(expr const & e, unsigned offset) {
        unsigned i = hash(e.hash_alloc(), offset) % m_capacity;
        if (m_cache[i].m_cell == e.raw() && m_cache[i].m_offset == offset) {
            return true;
        } else {
            if (m_cache[i].m_cell == nullptr)
                m_used.push_back(i);
            m_cache[i].m_cell   = e.raw();
            m_cache[i].m_offset = offset;
            return false;
        }
    }

    void clear() {
        for (unsigned i : m_used)
            m_cache[i].m_cell = nullptr;
        m_used.clear();
    }
};

MK_CACHE_STACK(for_each_cache, LEAN_DEFAULT_FOR_EACH_CACHE_CAPACITY)

class for_each_fn {
    for_each_cache_ref                          m_cache;
    std::function<bool(expr const &, unsigned)> m_f; // NOLINT

    void apply(expr const & e, unsigned offset) {
        buffer<pair<expr const &, unsigned>> todo;
        todo.emplace_back(e, offset);
        while (true) {
          begin_loop:
            if (todo.empty())
                break;
            check_interrupted();
            check_memory("expression traversal");
            auto p = todo.back();
            todo.pop_back();
            expr const & e  = p.first;
            unsigned offset = p.second;

            switch (e.kind()) {
            case expr_kind::Constant: case expr_kind::Var:
            case expr_kind::Sort:
                m_f(e, offset);
                goto begin_loop;
            default:
                break;
            }

            if (is_shared(e) && m_cache->visited(e, offset))
                goto begin_loop;

            if (!m_f(e, offset))
                goto begin_loop;

            switch (e.kind()) {
            case expr_kind::Constant: case expr_kind::Var:
            case expr_kind::Sort:
                goto begin_loop;
            case expr_kind::Meta: case expr_kind::Local:
                todo.emplace_back(mlocal_type(e), offset);
                goto begin_loop;
            case expr_kind::Macro: {
                unsigned i = macro_num_args(e);
                while (i > 0) {
                    --i;
                    todo.emplace_back(macro_arg(e, i), offset);
                }
                goto begin_loop;
            }
            case expr_kind::App:
                todo.emplace_back(app_arg(e), offset);
                todo.emplace_back(app_fn(e), offset);
                goto begin_loop;
            case expr_kind::Lambda: case expr_kind::Pi:
                todo.emplace_back(binding_body(e), offset + 1);
                todo.emplace_back(binding_domain(e), offset);
                goto begin_loop;
            }
        }
    }

public:
    for_each_fn(std::function<bool(expr const &, unsigned)> && f):m_f(f) {}        // NOLINT
    for_each_fn(std::function<bool(expr const &, unsigned)> const & f):m_f(f) {}   // NOLINT
    void operator()(expr const & e) { apply(e, 0); }
};

void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f) { // NOLINT
    return for_each_fn(f)(e);
}
}
