/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <utility>
#include <vector>
#include "util/rc.h"
#include "util/pair.h"
#include "util/debug.h"
#include "util/buffer.h"

namespace lean {

template<typename T, typename CMP>
class splay_tree : public CMP {
    struct node {
        node * m_left;
        node * m_right;
        T      m_value;
        MK_LEAN_RC();
        static void inc_ref(node * n) { if (n) n->inc_ref(); }
        static void dec_ref(node * n) { if (n) n->dec_ref(); }
        explicit node(T const & v, node * left = nullptr, node * right = nullptr):
            m_left(left), m_right(right), m_value(v), m_rc(0) {
            inc_ref(m_left);
            inc_ref(m_right);
        }
        node(node const & n):node(n.m_value, n.m_left, n.m_right) {}
        ~node() {
            dec_ref(m_left);
            dec_ref(m_right);
        }
        void dealloc() {
            delete this;
        }
        bool is_shared() const { return m_rc > 1; }

        static void display(std::ostream & out, node const * n) {
            if (n) {
                if (n->m_left == nullptr && n->m_right == nullptr) {
                    out << n->m_value << ":" << n->m_rc;
                } else {
                    out << "(" << n->m_value << ":" << n->m_rc << " ";
                    display(out, n->m_left);
                    out << " ";
                    display(out, n->m_right);
                    out << ")";
                }
            } else {
                out << "()";
            }
        }
    };

    node * m_ptr;

    int cmp(T const & v1, T const & v2) const {
        return CMP::operator()(v1, v2);
    }

    void update(node * n, node * l, node * r) {
        lean_assert(!n->is_shared());
        n->m_left  = l;
        n->m_right = r;
    }

    struct entry {
        bool m_right;
        node * m_node;
        entry(bool r, node * n):m_right(r), m_node(n) {}
    };

    void splay_to_top(std::vector<entry> & path, node * n) {
        lean_assert(!n->is_shared());
        while (path.size() > 1) {
            auto p_entry  = path.back(); path.pop_back();
            auto g_entry  = path.back(); path.pop_back();
            bool g_right  = g_entry.m_right;
            bool p_right  = p_entry.m_right;
            node * g = g_entry.m_node;
            node * p = p_entry.m_node;
            lean_assert(!g->is_shared());
            lean_assert(!p->is_shared());
            if (!g_right && !p_right) {
                // zig-zig left
                // (g (p (n A B) C) D) ==> (n A (p B (g C D)))
                lean_assert(g->m_left == p);
                node * A = n->m_left;
                node * B = n->m_right;
                node * C = p->m_right;
                node * D = g->m_right;
                update(g, C, D);
                update(p, B, g);
                update(n, A, p);
            } else if (!g_right && p_right) {
                // zig-zag left-right
                // (g (p A (n B C)) D) ==> (n (p A B) (g C D))
                lean_assert(g->m_left  == p);
                node * A = p->m_left;
                node * B = n->m_left;
                node * C = n->m_right;
                node * D = g->m_right;
                update(p, A, B);
                update(g, C, D);
                update(n, p, g);
            } else if (g_right && !p_right) {
                // zig-zag right-left
                // (g A (p (n B C) D)) ==> (n (g A B) (p C D))
                lean_assert(g->m_right == p);
                node * A = g->m_left;
                node * B = n->m_left;
                node * C = n->m_right;
                node * D = p->m_right;
                update(g, A, B);
                update(p, C, D);
                update(n, g, p);
            } else {
                lean_assert(g_right && p_right);
                lean_assert(g->m_right == p);
                // zig-zig right
                // (g A (p B (n C D))) ==> (n (p (g A B) C) D)
                node * A = g->m_left;
                node * B = p->m_left;
                node * C = n->m_left;
                node * D = n->m_right;
                update(g, A, B);
                update(p, g, C);
                update(n, p, D);
            }
        }
        lean_assert(!n->is_shared());
        if (path.size() == 1) {
            auto p_entry  = path.back(); path.pop_back();
            bool p_right  = p_entry.m_right;
            node * p      = p_entry.m_node;
            if (!p_right) {
                // zig left
                // (p (n A B) C) ==> (n A (p B C))
                node * A = n->m_left;
                node * B = n->m_right;
                node * C = p->m_right;
                update(p, B, C);
                update(n, A, p);
            } else {
                // zig right
                // (p A (n B C)) ==> (n (p A B) C)
                node * A = p->m_left;
                node * B = n->m_left;
                node * C = n->m_right;
                update(p, A, B);
                update(n, p, C);
            }
        }
        lean_assert(path.empty());
        lean_assert(!n->is_shared());
    }

    bool check_invariant(node const * n) const {
        if (n) {
            if (n->m_left) {
                check_invariant(n->m_left);
                lean_assert(cmp(n->m_left->m_value, n->m_value) < 0);
            }
            if (n->m_right) {
                check_invariant(n->m_right);
                lean_assert(cmp(n->m_value, n->m_right->m_value) < 0);
            }
        }
        return true;
    }

    void update_parent(std::vector<entry> const & path, node * child) {
        lean_assert(child);
        if (path.empty()) {
            child->inc_ref();
            node::dec_ref(m_ptr);
            m_ptr = child;
        } else {
            child->inc_ref();
            entry const & last = path.back();
            node * parent = last.m_node;
            if (last.m_right) {
                node::dec_ref(parent->m_right);
                parent->m_right = child;
            } else {
                node::dec_ref(parent->m_left);
                parent->m_left = child;
            }
        }
    }

    static void to_buffer(node const * n, buffer<T> & r) {
        if (n) {
            to_buffer(n->m_left, r);
            r.push_back(n->m_value);
            to_buffer(n->m_right, r);
        }
    }

public:
    splay_tree(CMP const & cmp = CMP()):CMP(cmp), m_ptr(nullptr) {}
    splay_tree(splay_tree const & s):CMP(s), m_ptr(s.m_ptr) { node::inc_ref(m_ptr); }
    splay_tree(splay_tree && s):CMP(s), m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~splay_tree() { node::dec_ref(m_ptr); }

    splay_tree & operator=(splay_tree const & s) { LEAN_COPY_REF(splay_tree, s); }
    splay_tree & operator=(splay_tree && s) { LEAN_MOVE_REF(splay_tree, s); }

    bool empty() const { return m_ptr == nullptr; }

    void insert(T const & v) {
        static thread_local std::vector<entry> path;
        node * n    = m_ptr;
        while (true) {
            if (n == nullptr) {
                n = new node(v);
                update_parent(path, n);
                break;
            } else {
                if (n->is_shared()) {
                    n = new node(*n);
                    update_parent(path, n);
                }
                lean_assert(!n->is_shared());
                int c = cmp(v, n->m_value);
                if (c < 0) {
                    path.push_back(entry(false, n));
                    n = n->m_left;
                } else if (c > 0) {
                    path.push_back(entry(true, n));
                    n = n->m_right;
                } else {
                    n->m_value = v;
                    break;
                }
            }
        }
        splay_to_top(path, n);
        m_ptr = n;
        lean_assert(check_invariant())
    }

    bool contains(T const & v) const {
        node const * n = m_ptr;
        while (true) {
            if (n == nullptr)
                return false;
            int c = cmp(v, n->m_value);
            if (c < 0)
                n = n->m_left;
            else if (c > 0)
                n = n->m_right;
            else
                return true;
        }
    }

    bool check_invariant() const {
        return check_invariant(m_ptr);
    }

    void to_buffer(buffer<T> & r) const {
        to_buffer(m_ptr, r);
    }

    friend std::ostream & operator<<(std::ostream & out, splay_tree const & t) {
        node::display(out, t.m_ptr);
        return out;
    }
};
template<typename T, typename CMP>
splay_tree<T, CMP> insert(splay_tree<T, CMP> & t, T const & v) { splay_tree<T, CMP> r(t); r.insert(v); return r; }
}
