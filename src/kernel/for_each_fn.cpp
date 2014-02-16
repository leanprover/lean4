/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/for_each_fn.h"

namespace lean {
void for_each_fn::apply(expr const & e, unsigned offset) {
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

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Var:
        case expr_kind::Sort:     case expr_kind::Macro:
            m_f(e, offset);
            goto begin_loop;
        default:
            break;
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
        case expr_kind::Constant: case expr_kind::Var:
        case expr_kind::Sort:     case expr_kind::Macro:
            goto begin_loop;
        case expr_kind::Meta: case expr_kind::Local:
            todo.emplace_back(mlocal_type(e), offset);
            goto begin_loop;
        case expr_kind::App:
            todo.emplace_back(app_arg(e), offset);
            todo.emplace_back(app_fn(e), offset);
            goto begin_loop;
        case expr_kind::Pair:
            todo.emplace_back(pair_type(e), offset);
            todo.emplace_back(pair_second(e), offset);
            todo.emplace_back(pair_first(e), offset);
            goto begin_loop;
        case expr_kind::Fst: case expr_kind::Snd:
            todo.emplace_back(proj_arg(e), offset);
            goto begin_loop;
        case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Sigma:
            todo.emplace_back(binder_body(e), offset + 1);
            todo.emplace_back(binder_domain(e), offset);
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
}
