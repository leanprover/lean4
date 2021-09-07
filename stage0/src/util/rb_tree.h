/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#if defined(__clang__)
#if defined(__has_warning) && __has_warning("-Wreturn-std-move")
#pragma clang diagnostic ignored "-Wreturn-std-move"
#endif
#endif
#include <utility>
#include <algorithm>
#include "runtime/optional.h"
#include "runtime/debug.h"
#include "runtime/buffer.h"
#include "util/rc.h"


namespace lean {
/**
   \brief Left-leaning Red-Black Trees

   It uses a O(1) copy operation. Different trees can share nodes.
   The sharing is thread-safe.

   \c CMP is a functional object for comparing values of type T.
   It must have a method
   <code>
         int operator()(T const & v1, T const & v2) const;
   </code>
   The method must return
   - -1 if <tt>v1 < v2</tt>,
   - 0  if <tt>v1 == v2</tt>,
   - 1  if <tt>v1 > v2</tt>
*/
template<typename T, typename CMP>
class rb_tree : private CMP {
    struct node_cell;
    struct node {
        node_cell * m_ptr;
        node():m_ptr(nullptr) {}
        node(node_cell * ptr):m_ptr(ptr) { if (m_ptr) ptr->inc_ref(); }
        node(node const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
        node(node && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
        ~node() { if (m_ptr) m_ptr->dec_ref(); }
        node & operator=(node const & n) { LEAN_COPY_REF(n); }
        node & operator=(node&& n) { LEAN_MOVE_REF(n); }
        operator bool() const { return m_ptr != nullptr; }
        bool is_shared() const { return m_ptr && m_ptr->get_rc() > 1; }
        bool is_red() const { return m_ptr && m_ptr->m_red; }
        bool is_black() const { return !is_red(); }
        node_cell * operator->() const { lean_assert(m_ptr); return m_ptr; }
        friend bool is_eqp(node const & n1, node const & n2) { return n1.m_ptr == n2.m_ptr; }
        friend void swap(node & n1, node & n2) { std::swap(n1.m_ptr, n2.m_ptr); }
        node steal() { node r; swap(r, *this); return r; }
    };

    struct node_cell {
        node m_left;
        node m_right;
        T    m_value;
        bool m_red;
        MK_LEAN_RC();
        void dealloc();
        node_cell(T const & v):m_value(v), m_red(true), m_rc(0) {}
        node_cell(node_cell const & s):m_left(s.m_left), m_right(s.m_right), m_value(s.m_value), m_red(s.m_red), m_rc(0) {}
    };

    bool check_cmp_result(T const & DEBUG_CODE(v1), T const & DEBUG_CODE(v2)) const {
        DEBUG_CODE(int n1 = CMP::operator()(v1, v2); int n2 = CMP::operator()(v2, v1););
        lean_assert((n1 < 0  && n2 > 0) || (n1 == 0 && n2 == 0) || (n1 > 0  && n2 < 0));
        return true;
    }

    int cmp(T const & v1, T const & v2) const {
        lean_cond_assert("rb_tree", check_cmp_result(v1, v2));
        return CMP::operator()(v1, v2);
    }

    static node ensure_unshared(node && n) {
        if (n.is_shared()) {
            return node(new node_cell(*n.m_ptr));
        } else {
            return n;
        }
    }

    static node set_black(node && n) {
        if (n.is_black())
            return n;
        node r = ensure_unshared(n.steal());
        r->m_red = false;
        return r;
    }

/* The following few methods cannot be static in debug mode because of assertions. */
#ifdef LEAN_DEBUG
#define LEAN_STATIC
#else
#define LEAN_STATIC static
#endif

    LEAN_STATIC node rotate_left(node && h) {
        lean_assert(!h.is_shared());
        node x = ensure_unshared(h->m_right.steal());
        lean_assert(!h->m_right); // x stole the ownership of h->m_right
        h->m_right = x->m_left;
        x->m_left  = h;
        x->m_red   = h->m_red;
        h->m_red   = true;
        lean_cond_assert("rb_tree", cmp(x->m_value, h->m_value) > 0);
        lean_cond_assert("rb_tree", !h->m_right.m_ptr || cmp(h->m_value, h->m_right->m_value) < 0);
        lean_cond_assert("rb_tree", !h->m_left.m_ptr || cmp(x->m_value, h->m_left->m_value) > 0);
        return x;
    }

    LEAN_STATIC node rotate_right(node && h) {
        lean_assert(!h.is_shared());
        node x = ensure_unshared(h->m_left.steal());
        lean_assert(!h->m_left); // x stole the ownership of h->m_left
        h->m_left  = x->m_right;
        x->m_right = h;
        x->m_red   = h->m_red;
        h->m_red   = true;
        lean_cond_assert("rb_tree", cmp(x->m_value, h->m_value) < 0);
        lean_cond_assert("rb_tree", !h->m_left.m_ptr || cmp(h->m_value, h->m_left->m_value) > 0);
        lean_cond_assert("rb_tree", !h->m_right.m_ptr || cmp(x->m_value, h->m_right->m_value) < 0);
        return x;
    }

    LEAN_STATIC node flip_colors(node && h) {
        lean_assert(!h.is_shared());
        h->m_red = !h->m_red;
        h->m_left  = ensure_unshared(h->m_left.steal());
        h->m_right = ensure_unshared(h->m_right.steal());
        h->m_left->m_red  = !h->m_left->m_red;
        h->m_right->m_red = !h->m_right->m_red;
        return h;
    }

    LEAN_STATIC node fixup(node && h) {
        lean_assert(!h.is_shared());
        if (h->m_right.is_red() && !h->m_left.is_red())
            h = rotate_left(h.steal());
        if (h->m_left.is_red() && h->m_left->m_left.is_red())
            h = rotate_right(h.steal());
        if (h->m_left.is_red() && h->m_right.is_red())
            h = flip_colors(h.steal());
        return h;
    }

    node insert(node && n, T const & v) {
        if (!n) {
            return node(new node_cell(v));
        }
        node h = ensure_unshared(n.steal());

        int c = cmp(v, h->m_value);
        if (c == 0)
            h->m_value = v;
        else if (c < 0)
            h->m_left  = insert(h->m_left.steal(), v);
        else
            h->m_right = insert(h->m_right.steal(), v);
        return fixup(h.steal());
    }

    LEAN_STATIC node move_red_left(node && h) {
        lean_assert(!h.is_shared());
        h = flip_colors(h.steal());
        if (h->m_right && h->m_right->m_left.is_red()) {
            h->m_right = rotate_right(h->m_right.steal());
            h          = rotate_left(h.steal());
            return flip_colors(h.steal());
        } else {
            return h;
        }
    }

    LEAN_STATIC node move_red_right(node && h) {
        lean_assert(!h.is_shared());
        h = flip_colors(h.steal());
        if (h->m_left && h->m_left->m_left.is_red()) {
            h          = rotate_right(h.steal());
            return flip_colors(h.steal());
        } else {
            return h;
        }
    }

    LEAN_STATIC node erase_min(node && n) {
        if (!n->m_left)
            return node();
        node h = ensure_unshared(n.steal());
        if (!h->m_left.is_red() && !h->m_left->m_left.is_red())
            h = move_red_left(h.steal());
        h->m_left = erase_min(h->m_left.steal());
        return fixup(h.steal());
    }

#undef LEAN_STATIC

    static T const * min(node const & n) {
        node_cell const * it = n.m_ptr;
        if (!it)
            return nullptr;
        while (it->m_left)
            it = it->m_left.m_ptr;
        return &it->m_value;
    }

    static T const * max(node const & n) {
        node_cell const * it = n.m_ptr;
        if (!it)
            return nullptr;
        while (it->m_right)
            it = it->m_right.m_ptr;
        return &it->m_value;
    }

    node erase(node && n, T const & v) {
        lean_assert(n);
        node h = ensure_unshared(n.steal());
        if (cmp(v, h->m_value) < 0) {
            lean_assert(h->m_left); // the tree contains v
            if (!h->m_left.is_red() && !h->m_left->m_left.is_red())
                h = move_red_left(h.steal());
            h->m_left = erase(h->m_left.steal(), v);
        } else {
            if (h->m_left.is_red())
                h = rotate_right(h.steal());
            if (cmp(v, h->m_value) == 0 && !h->m_right)
                return node();
            lean_assert(h->m_right);
            if (!h->m_right.is_red() && !h->m_right->m_left.is_red())
                h = move_red_right(h.steal());
            if (cmp(v, h->m_value) == 0) {
                h->m_value = *min(h->m_right);
                h->m_right = erase_min(h->m_right.steal());
            } else {
                h->m_right = erase(h->m_right.steal(), v);
            }
        }
        return fixup(h.steal());
    }

    template<typename F>
    static void for_each(F && f, node_cell const * n) {
        if (n) {
            for_each(f, n->m_left.m_ptr);
            f(n->m_value);
            for_each(f, n->m_right.m_ptr);
        }
    }

    template<typename F>
    static optional<T> find_if(F && f, node_cell const * n) {
        if (n) {
            if (auto r = find_if(f, n->m_left.m_ptr))
                return r;
            if (f(n->m_value))
                return optional<T>(n->m_value);
            if (auto r = find_if(f, n->m_right.m_ptr))
                return r;
        }
        return optional<T>();
    }

    template<typename F>
    static optional<T> back_find_if(F && f, node_cell const * n) {
        if (n) {
            if (auto r = back_find_if(f, n->m_right.m_ptr))
                return r;
            if (f(n->m_value))
                return optional<T>(n->m_value);
            if (auto r = back_find_if(f, n->m_left.m_ptr))
                return r;
        }
        return optional<T>();
    }

    template<typename F>
    void for_each_greater(T const & v, F && f, node_cell const * n) const {
        if (n) {
            int c = cmp(v, n->m_value);
            if (c == 0) {
                for_each(f, n->m_right.m_ptr);
            } else if (c > 0) {
                // v > n->m_value
                for_each_greater(v, f, n->m_right.m_ptr);
            } else {
                // v < n->m_value
                lean_assert(c < 0);
                for_each_greater(v, f, n->m_left.m_ptr);
                f(n->m_value);
                for_each(f, n->m_right.m_ptr);
            }
        }
    }

    T const * find_next_greater_or_equal(T const & v, node_cell const * n) const {
        if (n) {
            int c = cmp(v, n->m_value);
            if (c == 0) {
                return &n->m_value;
            } else if (c > 0) {
                // v > n->m_value
                return find_next_greater_or_equal(v, n->m_right.m_ptr);
            } else {
                // v < n->m_value
                if (auto on_left = find_next_greater_or_equal(v, n->m_left.m_ptr)) {
                    return on_left;
                } else {
                    return &n->m_value;
                }
            }
        } else {
            return nullptr;
        }
    }

    static void display(std::ostream & out, node_cell const * n) {
        if (n) {
            out << "(";
            if (n->m_red)
                out << "*";
            out << n->m_value << " ";
            display(out, n->m_left.m_ptr);
            out << " ";
            display(out, n->m_right.m_ptr);
            out << ")";
        } else {
            out << "nil";
        }
    }

    static unsigned get_depth(node_cell const * n) {
        if (n)
            return std::max(get_depth(n->m_left.m_ptr), get_depth(n->m_right.m_ptr)) + 1;
        else
            return 0;
    }

    static void to_buffer(node_cell const * n, buffer<T> & r) {
        if (n) {
            to_buffer(n->m_left.m_ptr, r);
            r.push_back(n->m_value);
            to_buffer(n->m_right.m_ptr, r);
        }
    }

    bool check_invariant(node_cell const * n, unsigned curr_black, optional<unsigned> & num_black) const {
        // We check:
        //  1) the nodes are really ordered, that is, left->value < n->value < right->value
        //  2) there are no two consecutive red nodes
        //  3) every path has the same number of black nodes
        if (n) {
            if (!n->m_red)
                curr_black++;
            if (n->m_left) {
                lean_assert(!n->m_red || !n->m_left.is_red());
                check_invariant(n->m_left.m_ptr, curr_black, num_black);
                lean_assert(cmp(n->m_left->m_value, n->m_value) < 0);
            }
            if (n->m_right) {
                lean_assert(!n->m_red || !n->m_right.is_red());
                check_invariant(n->m_right.m_ptr, curr_black, num_black);
                lean_assert(cmp(n->m_value, n->m_right->m_value) < 0);
            }
        } else {
            // end of a path
            if (num_black) {
                lean_assert(curr_black == *num_black);
            } else {
                num_black = curr_black;
            }
        }
        return true;
    }

    node m_root;

public:
    rb_tree(CMP const & cmp = CMP()):CMP(cmp) {}
    rb_tree(rb_tree const & s):CMP(s), m_root(s.m_root) {}
    rb_tree(rb_tree && s):CMP(s), m_root(s.m_root) {}
    explicit rb_tree(buffer<T> const & s) {
        for (auto const & v : s)
            insert(v);
    }
    explicit rb_tree(T const & v) {
        insert(v);
    }

    rb_tree & operator=(rb_tree const & s) { m_root = s.m_root; return *this; }
    rb_tree & operator=(rb_tree && s) { m_root = s.m_root; return *this; }

    CMP const & get_cmp() const { return *this; }

    unsigned get_rc() const { return m_root ? m_root->get_rc() : 0; }

    void insert(T const & v) {
        lean_cond_assert("rb_tree", check_invariant());
        m_root = set_black(insert(m_root.steal(), v));
        lean_cond_assert("rb_tree", check_invariant());
    }

    void erase_min() {
        lean_cond_assert("rb_tree", check_invariant());
        m_root = set_black(erase_min(m_root.steal()));
        lean_cond_assert("rb_tree", check_invariant());
    }

    void erase_core(T const & v) {
        lean_cond_assert("rb_tree", check_invariant());
        lean_assert(contains(v));
        m_root = set_black(erase(m_root.steal(), v));
        lean_cond_assert("rb_tree", check_invariant());
    }

    void erase(T const & v) {
        if (contains(v))
            erase_core(v);
    }

    T const * find(T const & v) const {
        node_cell const * h = m_root.m_ptr;
        while (h) {
            int c = cmp(v, h->m_value);
            if (c == 0)
                return &(h->m_value);
            else if (c < 0)
                h = h->m_left.m_ptr;
            else
                h = h->m_right.m_ptr;
        }
        return nullptr;
    }

    T const * min() const { return min(m_root); }
    T const * max() const { return max(m_root); }
    bool contains(T const & v) const { return find(v) != nullptr; }

    template<typename F>
    void for_each(F && f) const {
        node r = m_root;
        for_each(f, r.m_ptr);
    }

    template<typename F>
    optional<T> find_if(F && f) const {
        node r = m_root;
        return find_if(f, r.m_ptr);
    }

    /* Similar to find_if, but searches keys backwards from greatest to least */
    template<typename F>
    optional<T> back_find_if(F && f) const {
        node r = m_root;
        return back_find_if(f, r.m_ptr);
    }

    template<typename F>
    void for_each_greater(T const & v, F && f) const {
        node r = m_root.m_ptr;
        for_each_greater(v, f, r.m_ptr);
    }

    T const * find_next_greater_or_equal(T const & v) const {
        return find_next_greater_or_equal(v, m_root.m_ptr);
    }

    // For debugging purposes
    void display(std::ostream & out) const { display(out, m_root.m_ptr); }

    unsigned get_depth() const { return get_depth(m_root.m_ptr); }

    unsigned size() const {
        unsigned r = 0;
        for_each([&](T const & ){ r = r + 1; });
        return r;
    }

    bool empty() const { return m_root.m_ptr == nullptr; }

    void clear() { m_root = node(); }

    friend std::ostream & operator<<(std::ostream & out, rb_tree const & t) {
        t.display(out);
        return out;
    }

    bool check_invariant() const {
        optional<unsigned> num_black;
        return check_invariant(m_root.m_ptr, 0, num_black);
    }

    /**
        \brief Copy the contents of this tree to the given buffer.
        The elements will be stored in increasing order.
    */
    void to_buffer(buffer<T> & r) const {
        to_buffer(m_root.m_ptr, r);
    }

    void merge(rb_tree const & s) {
        if (empty())
            *this = s;
        else if (!is_eqp(*this, s))
            s.for_each([&](T const & v) { insert(v); });
    }

    bool is_superset(rb_tree const & s) const {
        return !s.find_if([&](T const & v) { return !contains(v); });
    }

    bool is_strict_superset(rb_tree const & s) const {
        if (!is_superset(s))
            return false;
        return !s.is_superset(*this);
    }

    void remove(rb_tree const & s) {
        s.for_each([&](T const & v) { erase(v); });
    }

    friend bool is_eqp(rb_tree const & s1, rb_tree const & s2) { return is_eqp(s1.m_root, s2.m_root); }

    class iterator {
        buffer<node_cell const *> m_path;

        void push_left(node_cell const * it) {
            while (it) {
                m_path.push_back(it);
                it = it->m_left.m_ptr;
            }
        }

    public:
        iterator(rb_tree const & t) {
            push_left(t.m_root.m_ptr);
        }

        bool has_next() const { return !m_path.empty(); }

        T const & next() {
            lean_assert(has_next());
            node_cell const * it = m_path.back();
            node_cell const * r  = it;
            /* if you can walk right, walk right, then fully left.
               otherwise, walk up until you come from left. */
            if (it->m_right.m_ptr != nullptr) {
                push_left(it->m_right.m_ptr);
                return r->m_value;
            } else {
                m_path.pop_back();
                while (!m_path.empty()) {
                    node_cell const * p = m_path.back();
                    if (p->m_left.m_ptr == it)
                        break;
                    it = p;
                    m_path.pop_back();
                }
                return r->m_value;
            }
        }
    };

    /* Return true iff this and other have the same set of elements with respect to CMP.
       This method assumes the cmp for this and other are the same. */
    bool equal_elems(rb_tree const & other) const {
        iterator it1(*this);
        iterator it2(other);
        while (it1.has_next() && it2.has_next()) {
            if (cmp(it1.next(), it2.next()) != 0)
                return false;
        }
        return !it1.has_next() && !it2.has_next();
    }
};

template<typename T, typename CMP>
bool operator==(rb_tree<T, CMP> const & s1, rb_tree<T, CMP> const & s2) {
    return s1.is_superset(s2) && s2.is_superset(s1);
}

template<typename T, typename CMP>
void rb_tree<T, CMP>::node_cell::dealloc() {
    delete this;
}

template<typename T, typename CMP>
rb_tree<T, CMP> insert(rb_tree<T, CMP> const & t, T const & v) { rb_tree<T, CMP> r(t); r.insert(v); return r; }
template<typename T, typename CMP>
rb_tree<T, CMP> erase(rb_tree<T, CMP> const & t, T const & v) { rb_tree<T, CMP> r(t); r.erase(v); return r; }

struct unsigned_cmp {
    typedef unsigned type;
    int operator()(unsigned i1, unsigned i2) const { return i1 < i2 ? -1 : (i1 == i2 ? 0 : 1); }
};
struct unsigned_rev_cmp {
    typedef unsigned type;
    int operator()(unsigned i1, unsigned i2) const { return i1 > i2 ? -1 : (i1 == i2 ? 0 : 1); }
};
struct int_cmp {
    typedef int type;
    int operator()(int i1, int i2) const { return i1 < i2 ? -1 : (i1 == i2 ? 0 : 1); }
};
struct double_cmp {
    typedef double type;
    int operator()(double i1, double i2) const { return i1 < i2 ? -1 : (i1 > i2 ? 1 : 0); }
};
template<typename C1, typename C2>
struct pair_cmp {
    C1 m_c1;
    C2 m_c2;
    typedef std::pair<typename C1::type, typename C2::type> type;
    int operator()(type const & p1, type const & p2) const {
        int r1 = m_c1(p1.first, p2.first);
        if (r1 != 0) return r1;
        return m_c2(p1.second, p2.second);
    }
    pair_cmp(C1 const & c1 = C1(), C2 const & c2 = C2()):m_c1(c1), m_c2(c2) {}
};
}
