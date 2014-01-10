/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <tuple>
#include "util/buffer.h"
#include "util/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "kernel/update_expr.h"

namespace lean {
/**
   \brief Default replace_fn postprocessor functional object. It is a
   do-nothing object.
*/
class default_replace_postprocessor {
public:
    void operator()(expr const &, expr const &) {}
};

/**
   \brief Functional for applying <tt>F</tt> to the subexpressions of a given expression.

   The signature of \c F is
   expr const &, unsigned -> expr

   F is invoked for each subexpression \c s of the input expression e.
   In a call <tt>F(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s.

   P is a "post-processing" functional object that is applied to each
   pair (old, new)
*/
template<typename F, typename P = default_replace_postprocessor>
class replace_fn {
    static_assert(std::is_same<typename std::result_of<F(expr const &, unsigned)>::type, expr>::value,
                  "replace_fn: return type of F is not expr");
    // the return type of P()(e1, e2) should be void
    static_assert(std::is_same<typename std::result_of<decltype(std::declval<P>())(expr const &, expr const &)>::type,
                  void>::value,
                  "The return type of P()(e1, e2) is not void");

    struct frame {
        expr       m_expr;
        unsigned   m_offset;
        bool       m_shared;
        unsigned   m_index;
        frame(expr const & e, unsigned o, bool s):m_expr(e), m_offset(o), m_shared(s), m_index(0) {}
    };
    typedef buffer<frame>  frame_stack;
    typedef buffer<expr>   result_stack;

    expr_cell_offset_map<expr> m_cache;
    F                          m_f;
    P                          m_post;
    frame_stack                m_fs;
    result_stack               m_rs;

    static bool is_atomic(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
        case expr_kind::Var: case expr_kind::MetaVar:
            return true;
        default:
            return false;
        }
    }

    void save_result(expr const & e, expr const & r, unsigned offset, bool shared) {
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
    bool visit(expr const & e, unsigned offset) {
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
    bool check_index(frame & f, unsigned idx) {
        if (f.m_index == idx) {
            f.m_index++;
            return true;
        } else {
            return false;
        }
    }

    expr const & rs(int i) {
        lean_assert(i < 0);
        return m_rs[m_rs.size() + i];
    }

    void pop_rs(unsigned num) {
        m_rs.shrink(m_rs.size() - num);
    }

public:
    replace_fn(F const & f, P const & p = P()):
        m_f(f),
        m_post(p) {
    }

    expr operator()(expr const & e) {
        expr r;
        visit(e, 0);
        while (!m_fs.empty()) {
          begin_loop:
            check_interrupted();
            frame & f = m_fs.back();
            expr const & e   = f.m_expr;
            unsigned offset  = f.m_offset;
            switch (e.kind()) {
            case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value: case expr_kind::Var: case expr_kind::MetaVar:
                lean_unreachable(); // LCOV_EXCL_LINE
            case expr_kind::App: {
                unsigned num = num_args(e);
                while (f.m_index < num) {
                    expr const & c = arg(e, f.m_index);
                    f.m_index++;
                    if (!visit(c, offset))
                        goto begin_loop;
                }
                r = update_app(e, num, m_rs.end() - num_args(e));
                pop_rs(num);
                break;
            }
            case expr_kind::HEq:
                if (check_index(f, 0) && !visit(heq_lhs(e), offset))
                    goto begin_loop;
                if (check_index(f, 1) && !visit(heq_rhs(e), offset))
                    goto begin_loop;
                r = update_heq(e, rs(-2), rs(-1));
                pop_rs(2);
                break;
            case expr_kind::Pi: case expr_kind::Lambda:
                if (check_index(f, 0) && !visit(abst_domain(e), offset))
                    goto begin_loop;
                if (check_index(f, 1) && !visit(abst_body(e), offset + 1))
                    goto begin_loop;
                r = update_abstraction(e, rs(-2), rs(-1));
                pop_rs(2);
                break;
            case expr_kind::Let:
                if (check_index(f, 0) && let_type(e) && !visit(*let_type(e), offset))
                    goto begin_loop;
                if (check_index(f, 1) && !visit(let_value(e), offset))
                    goto begin_loop;
                if (check_index(f, 2) && !visit(let_body(e), offset + 1))
                    goto begin_loop;
                if (let_type(e)) {
                    r = update_let(e, some_expr(rs(-3)), rs(-2), rs(-1));
                    pop_rs(3);
                } else {
                    r = update_let(e, none_expr(), rs(-2), rs(-1));
                    pop_rs(2);
                }
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

    void clear() {
        m_cache.clear();
        m_fs.clear();
        m_rs.clear();
    }
};

template<typename F>
expr replace(expr const & e, F f) {
    return replace_fn<F>(f)(e);
}

template<typename F, typename P>
expr replace(expr const & e, F f, P p) {
    return replace_fn<F, P>(f, p)(e);
}
}
