/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/buffer.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"

namespace lean {
/**
   \brief Template for implementing expression visitors.
   The argument \c F must be a function object containing the method
   <code>
   void operator()(expr const & e, unsigned offset)
   </code>
   The \c offset is the number of binders under which \c e occurs.
*/
template<typename F, bool CacheAtomic = false>
class for_each_fn {
    std::unique_ptr<expr_cell_offset_set> m_visited;
    F                                     m_f;
    static_assert(std::is_same<typename std::result_of<F(expr const &, unsigned)>::type, bool>::value,
                  "for_each_fn: return type of m_f is not bool");

    void apply(expr const & e, unsigned offset) {
        buffer<std::pair<expr const &, unsigned>> todo;
        todo.emplace_back(e, offset);
        while (true) {
          begin_loop:
            if (todo.empty())
                break;
            auto p = todo.back();
            todo.pop_back();
            expr const & e  = p.first;
            unsigned offset = p.second;
            if (!CacheAtomic) {
                switch (e.kind()) {
                case expr_kind::Constant:
                    if (!const_type(e)) {
                        // only constants without cached types are considered atomic
                        m_f(e, offset);
                        goto begin_loop;
                    }
                    break;
                case expr_kind::Type: case expr_kind::Value:
                case expr_kind::Var: case expr_kind::MetaVar:
                    m_f(e, offset);
                    goto begin_loop;
                default:
                    break;
                }
            }

            if (is_shared(e)) {
                expr_cell_offset p(e.raw(), offset);
                if (!m_visited)
                    m_visited.reset(new expr_cell_offset_set());
                if (m_visited->find(p) != m_visited->end())
                    goto begin_loop;
                m_visited->insert(p);
            }

            if (!m_f(e, offset))
                goto begin_loop;

            switch (e.kind()) {
            case expr_kind::Constant:
                if (const_type(e))
                    todo.emplace_back(*const_type(e), offset);
                goto begin_loop;
            case expr_kind::Type: case expr_kind::Value:
            case expr_kind::Var: case expr_kind::MetaVar:
                goto begin_loop;
            case expr_kind::App: {
                auto it    = end_args(e);
                auto begin = begin_args(e);
                while (it != begin) {
                    --it;
                    todo.emplace_back(*it, offset);
                }
                goto begin_loop;
            }
            case expr_kind::Lambda:
            case expr_kind::Pi:
                todo.emplace_back(abst_body(e), offset + 1);
                todo.emplace_back(abst_domain(e), offset);
                goto begin_loop;
            case expr_kind::Let:
                todo.emplace_back(let_body(e), offset + 1);
                todo.emplace_back(let_value(e), offset);
                if (let_type(e))
                    todo.emplace_back(*let_type(e), offset);
                goto begin_loop;
            }
        }
    }
public:
    for_each_fn(F const & f):m_f(f) {}
    void operator()(expr const & e) { apply(e, 0); }
};

template<typename F>
void for_each(expr const & e, F f) {
    return for_each_fn<F>(f)(e);
}
}
