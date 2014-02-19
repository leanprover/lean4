/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/replace_fn.h"

namespace lean {
void replace_fn::save_result(expr const & e, expr const & r, unsigned offset, bool shared) {
    if (shared)
        m_cache.insert(std::make_pair(expr_cell_offset(e.raw(), offset), r));
    m_post(e, r);
    m_rs.push_back(r);
}

/**
   \brief Visit \c e at the given offset. Return true iff the result is on the
   result stack \c m_rs. Return false iff a new frame was pushed on the stack \c m_fs.
   The idea is that after the frame is processed, the result will be on the result stack.
*/
bool replace_fn::visit(expr const & e, unsigned offset) {
    bool shared = false;
    if (is_shared(e)) {
        expr_cell_offset p(e.raw(), offset);
        auto it = m_cache.find(p);
        if (it != m_cache.end()) {
            m_rs.push_back(it->second);
            return true;
        }
        shared = true;
    }

    expr r = m_f(e, offset);
    if (is_atomic(r) || !is_eqp(e, r)) {
        save_result(e, r, offset, shared);
        return true;
    } else {
        m_fs.emplace_back(e, offset, shared);
        return false;
    }
}

/**
   \brief Return true iff <tt>f.m_index == idx</tt>.
   When the result is true, <tt>f.m_index</tt> is incremented.
*/
bool replace_fn::check_index(frame & f, unsigned idx) {
    if (f.m_index == idx) {
        f.m_index++;
        return true;
    } else {
        return false;
    }
}

expr const & replace_fn::rs(int i) {
    lean_assert(i < 0);
    return m_rs[m_rs.size() + i];
}

void replace_fn::pop_rs(unsigned num) {
    m_rs.shrink(m_rs.size() - num);
}

expr replace_fn::operator()(expr const & e) {
    expr r;
    visit(e, 0);
    while (!m_fs.empty()) {
      begin_loop:
        check_interrupted();
        frame & f = m_fs.back();
        expr const & e   = f.m_expr;
        unsigned offset  = f.m_offset;
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Sort:
        case expr_kind::Macro:    case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Meta:     case expr_kind::Local:
            if (check_index(f, 0) && !visit(mlocal_type(e), offset))
                goto begin_loop;
            r = update_mlocal(e, rs(-1));
            pop_rs(1);
            break;
        case expr_kind::Pair:
            if (check_index(f, 0) && !visit(pair_first(e), offset))
                goto begin_loop;
            if (check_index(f, 1) && !visit(pair_second(e), offset))
                goto begin_loop;
            if (check_index(f, 2) && !visit(pair_type(e), offset))
                goto begin_loop;
            r = update_pair(e, rs(-3), rs(-2), rs(-1));
            pop_rs(3);
            break;
        case expr_kind::Fst: case expr_kind::Snd:
            if (check_index(f, 0) && !visit(proj_arg(e), offset))
                goto begin_loop;
            r = update_proj(e, rs(-1));
            pop_rs(1);
            break;
        case expr_kind::App:
            if (check_index(f, 0) && !visit(app_fn(e), offset))
                goto begin_loop;
            if (check_index(f, 1) && !visit(app_arg(e), offset))
                goto begin_loop;
            r = update_app(e, rs(-2), rs(-1));
            pop_rs(2);
            break;
        case expr_kind::Sigma: case expr_kind::Pi: case expr_kind::Lambda:
            if (check_index(f, 0) && !visit(binder_domain(e), offset))
                goto begin_loop;
            if (check_index(f, 1) && !visit(binder_body(e), offset + 1))
                goto begin_loop;
            r = update_binder(e, rs(-2), rs(-1));
            pop_rs(2);
            break;
        case expr_kind::Let:
            if (check_index(f, 0) && !visit(let_type(e), offset))
                goto begin_loop;
            if (check_index(f, 1) && !visit(let_value(e), offset))
                goto begin_loop;
            if (check_index(f, 2) && !visit(let_body(e), offset + 1))
                goto begin_loop;
            r = update_let(e, rs(-3), rs(-2), rs(-1));
            pop_rs(3);
            break;
        }
        save_result(e, r, offset, f.m_shared);
        m_fs.pop_back();
    }
    lean_assert(m_rs.size() == 1);
    r = m_rs.back();
    m_rs.pop_back();
    return r;
}

void replace_fn::clear() {
    m_cache.clear();
    m_fs.clear();
    m_rs.clear();
}
}
