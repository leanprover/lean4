/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "util/optional.h"

namespace lean {
/** \brief (template for) Union-find datastructure that "explains" implied equalities.
    We use functional datastructures to be able to have a O(1) copy operation.

    Each join/union is decorated with a justification.

    \c cmp implements a total order on \c node. That is, it provides the method:
         int operator()(node const & n1, node const & n2) const
    s.t. the result is negative when n1 < n2, 0 if n1 == n2, and positive if n1 > n2.

    The implementation also provides a method to traverse the elements of an equivalence
    class. The implementation is based on a datastructure used in the Simplify theorem prover.

    Since it provides extra functionality, it does not implement the O(n*alpha(n)) amortized time
    per operation algorithm.
*/
template<typename node, typename jst, typename cmp>
class union_find : private cmp {
    rb_map<node, node, cmp>            m_root;
    rb_map<node, node, cmp>            m_next;
    rb_map<node, unsigned, cmp>        m_rank;
    rb_map<node, pair<node, jst>, cmp> m_jst;

    bool is_equal(node const & n1, node const & n2) const {
        return cmp::operator()(n1, n2) == 0;
    }

    unsigned rank(node const & n) const {
        if (auto r = m_rank.find(n))
            return *r;
        else
            return 0;
    }
    void set_rank(node const & n, unsigned r) { m_rank.insert(n, r); }

    node const & root(node const & n) const {
        if (auto r = m_root.find(n))
            return *r;
        else
            return n;
    }
    void set_root(node const & n, node const & r) { m_root.insert(n, r); }

    node const & next(node const & n) const {
        if (auto r = m_next.find(n))
            return *r;
        else
            return n;
    }
    void set_next(node const & n, node const & nx) { m_next.insert(n, nx); }
    void set_justification(node const & n, node const & t, jst const & j) { m_jst.insert(n, mk_pair(t, j)); }

    // for debugging purposes only
    bool check_inv(node const & n) const {
        node r      = root(n);
        unsigned sz = size(r);
        node it     = n;
        do {
            lean_assert_eq(root(it), r);
            lean_assert(reaches(it, r));
            lean_assert(size(it), sz);
            it = next(it);
        } while (!is_equal(it, n));
        return true;
    }

    void join_core(node const & n1, node r1, node const & n2, node r2, jst const & j) {
        // r1 will be the root of the resulting equivalence class.
        DEBUG_CODE(unsigned sz1 = size(n1); unsigned sz2 = size(n2););
        // Step 1) update m_jst
        //
        // Given justification paths
        //   n1 -> ... -> r1
        //   n2 -> ... -> r2
        // we generate the path
        //   r2 -> ... -> n2 -> n1 -> ... -> r1
        buffer<pair<node, jst>> trace;
        node it2 = n2;
        while (pair<node, jst> const * p = m_jst.find(it2)) {
            trace.push_back(*p);
            it2 = p->first;
        }
        lean_assert(is_equal(it2, r2));
        unsigned i = trace.size();
        while (i > 1) {
            --i;
            set_justification(trace[i].first, trace[i-1].first, trace[i].second);
        }
        if (i > 0) {
            set_justification(trace[0].first, n2, trace[0].second);
        }
        set_justification(n2, n1, j);

        // Step 2) update m_root of nodes in n2 equivalence class to r1
        it2 = n2;
        do {
            set_root(it2, r1);
            it2 = next(it2);
        } while (!is_equal(it2, n2));

        // Step 3) update m_next of r1 and r2
        node next1 = next(r1);
        node next2 = next(r2);
        set_next(r1, next2);
        set_next(r2, next1);

        lean_assert(check_inv(r1));
        lean_assert_eq(size(n1), sz1 + sz2);
    }

    /** \brief Return true if \c s reaches \c r by following m_jst edges */
    bool reaches(node const & s, node const & r) const {
        node it = s;
        while (true) {
            if (is_equal(it, r))
                return true;
            pair<node, jst> const * p = m_jst.find(it);
            if (p) {
                it = p->first;
            } else {
                return false;
            }
        }
    }

    void explain_core(node const & n1, node const & n2, node const & r, buffer<jst> & js) const {
        lean_assert(is_equal(root(n1), r));
        lean_assert(is_equal(root(n2), r));
        node it1 = n1;
        while (true) {
            if (reaches(n2, it1)) {
                // it is the common in the paths n1 -> r and n2 -> r
                node it2 = n2;
                unsigned sz1 = js.size();
                while (true) {
                    if (is_equal(it2, it1)) {
                        std::reverse(js.begin() + sz1, js.end());
                        return;
                    }
                    pair<node, jst> const * p = m_jst.find(it2);
                    lean_assert(p);
                    js.push_back(p->second);
                    it2 = p->first;
                }
            } else {
                pair<node, jst> const * p = m_jst.find(it1);
                lean_assert(p);
                js.push_back(p->second);
                it1 = p->first;
            }
        }
    }

public:
    union_find(cmp const & c = cmp()):cmp(c) {}

    /** \brief Merge the equivalence class of \c n1 with \c n2 using justification \c j. */
    void join(node const & n1, node const & n2, jst const & j) {
        node const & r1 = root(n1);
        node const & r2 = root(n2);
        if (is_equal(r1, r2))
            return;
        unsigned k1 = rank(n1);
        unsigned k2 = rank(n2);
        if (k1 > k2) {
            join_core(n1, r1, n2, r2, j);
        } else if (k1 == k2) {
            join_core(n1, r1, n2, r2, j);
            set_rank(n1, k1+1);
        } else {
            join_core(n2, r2, n1, r1, j);
        }
    }

    /** \brief Return the size of the equivalence class containing \c n */
    unsigned size(node const & n) const {
        unsigned r = 0;
        node it    = n;
        do {
            lean_assert(is_eq(it, n));
            r++;
            it = next(it);
        } while (!is_equal(it, n));
        return r;
    }

    /** \brief Return the representative for the equivalence class containing \c n. */
    node rep(node const & n) const { return root(n); }

    /** \brief Return true iff \c n1 and \c n2 are in the same equivalence class. */
    bool is_eq(node const & n1, node const & n2) const { return is_equal(rep(n1), rep(n2)); }

    /** \brief For each node \c m in the equivalence class of \c n, execute <tt>f(m)</tt> */
    template<typename F>
    void for_each(node const & n, F f) const {
        node it = n;
        do {
            lean_assert(is_eq(it, n));
            f(it);
            it = next(it);
        } while (!is_equal(it, n));
    }

    /** \brief If is_eq(n1, n2), then return true and store the justifications that can be used to produce
        a transitivity+symmetry proof for n1 = n2 */
    bool explain(node const & n1, node const & n2, buffer<jst> & js) const {
        node r1 = root(n1);
        node r2 = root(n2);
        if (is_equal(r1, r2)) {
            if (rank(r1) >= rank(r2)) {
                explain_core(n1, n2, r1, js);
            } else {
                explain_core(n2, n1, r1, js);
                std::reverse(js.begin(), js.end());
            }
            return true;
        } else {
            return false;
        }
    }
};
}
