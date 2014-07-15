/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "kernel/replace_fn.h"

#ifndef LEAN_DEFAULT_REPLACE_CACHE_CAPACITY
#define LEAN_DEFAULT_REPLACE_CACHE_CAPACITY 1024*32
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
        if (m_cache[i].m_cell == e.raw())
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

MK_THREAD_LOCAL_GET(replace_cache, get_replace_cache, LEAN_DEFAULT_REPLACE_CACHE_CAPACITY)

struct replace_cache_reset {
    ~replace_cache_reset() { get_replace_cache().clear(); }
};

/**
   \brief Functional for applying <tt>F</tt> to the subexpressions of a given expression.

   The signature of \c F is
   expr const &, unsigned -> optional(expr)

   F is invoked for each subexpression \c s of the input expression e.
   In a call <tt>F(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if F return none_expr
*/
class replace_fn {
    struct frame {
        expr       m_expr;
        unsigned   m_offset;
        bool       m_shared;
        unsigned   m_index;
        frame(expr const & e, unsigned o, bool s):m_expr(e), m_offset(o), m_shared(s), m_index(0) {}
    };
    typedef buffer<frame>  frame_stack;
    typedef buffer<expr>   result_stack;

    std::function<optional<expr>(expr const &, unsigned)> m_f;
    frame_stack                                           m_fs;
    result_stack                                          m_rs;
    replace_cache &                                       m_cache;

    void save_result(expr const & e, expr const & r, unsigned offset, bool shared) {
        if (shared)
            m_cache.insert(e, offset, r);
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
            if (auto r = m_cache.find(e, offset)) {
                m_rs.push_back(*r);
                return true;
            }
            shared = true;
        }

        optional<expr> r = m_f(e, offset);
        if (r) {
            save_result(e, *r, offset, shared);
            return true;
        } else if (is_atomic(e)) {
            save_result(e, e, offset, shared);
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
    template<typename F>
    replace_fn(F const & f):m_f(f), m_cache(get_replace_cache()) {}

    expr operator()(expr const & e) {
        replace_cache_reset reset;
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
            case expr_kind::Var:
                lean_unreachable(); // LCOV_EXCL_LINE
            case expr_kind::Meta:     case expr_kind::Local:
                if (check_index(f, 0) && !visit(mlocal_type(e), offset))
                    goto begin_loop;
                r = update_mlocal(e, rs(-1));
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
            case expr_kind::Pi: case expr_kind::Lambda:
                if (check_index(f, 0) && !visit(binding_domain(e), offset))
                    goto begin_loop;
                if (check_index(f, 1) && !visit(binding_body(e), offset + 1))
                    goto begin_loop;
                r = update_binding(e, rs(-2), rs(-1));
                pop_rs(2);
                break;
            case expr_kind::Macro:
                while (f.m_index < macro_num_args(e)) {
                    unsigned idx = f.m_index;
                    f.m_index++;
                    if (!visit(macro_arg(e, idx), offset))
                        goto begin_loop;
                }
                r = update_macro(e, macro_num_args(e), &rs(-macro_num_args(e)));
                pop_rs(macro_num_args(e));
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
};

expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f) {
    return replace_fn(f)(e);
}
}
