/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include "util/lp/permutation_matrix.h"
namespace lean {
template <typename T, typename X> permutation_matrix<T, X>::permutation_matrix(unsigned length): m_permutation(length), m_rev(length) {
    lean_assert(length > 0);
    for (unsigned i = 0; i < length; i++) { // do not change the direction of the loop because of the vectorization bug in clang3.3
        m_permutation[i] = m_rev[i] = i;
    }
}

template <typename T, typename X> permutation_matrix<T, X>::permutation_matrix(unsigned length, std::vector<unsigned> const & values): m_permutation(length), m_rev(length) {
    for (unsigned i = 0; i < length; i++) {
        set_val(i, values[i]);
    }
}
// create a unit permutation of the given length
template <typename T, typename X> void permutation_matrix<T, X>::init(unsigned length) {
    m_permutation.resize(length);
    m_rev.resize(length);
    for (unsigned i = 0; i < length; i++) {
        m_permutation[i] = m_rev[i] = i;
    }
}

#ifdef LEAN_DEBUG
template <typename T, typename X> void permutation_matrix<T, X>::print(std::ostream & out) const {
    out << "[";
    for (unsigned i = 0; i < size(); i++) {
        out << m_permutation[i];
        if (i < size() - 1) {
            out << ",";
        } else {
            out << "]";
        }
    }
    out << std::endl;
}
#endif

template <typename T, typename X>template <typename L>
void permutation_matrix<T, X>::apply_from_left_perm(std::vector<L> & w) {
#ifdef LEAN_DEBUG
    // dense_matrix<L, X> deb(*this);
    // L * deb_w = clone_vector<L>(w, row_count());
    // deb.apply_from_left(deb_w);
#endif
    std::vector<L> t(size());
    unsigned i = size();
    while (i-- > 0) {
        t[i] = w[m_permutation[i]];
    }
    i = size();
    while (i-- > 0) {
        w[i] = t[i];
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<L>(deb_w, w, row_count()));
    // delete [] deb_w;
#endif
}

template <typename T, typename X>template <typename L>
void permutation_matrix<T, X>::apply_from_left_perm(indexed_vector<L> & w, lp_settings &) {
#ifdef LEAN_DEBUG
    // dense_matrix<T, L> deb(*this);
    // T * deb_w = clone_vector<T>(w.m_data, row_count());
    // deb.apply_from_right(deb_w);
#endif
    std::vector<L> t(w.m_index.size());
    std::vector<unsigned> tmp_index(w.m_index.size());
    copy_aside(t, tmp_index, w);
    clear_data(w);
    // set the new values
    for (unsigned i = t.size(); i > 0;) {
        i--;
        unsigned j = m_rev[tmp_index[i]];
        w[j] = t[i];
        w.m_index[i] = j;
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<T>(deb_w, w.m_data, row_count()));
    // delete [] deb_w;
#endif
}


template <typename T, typename X> void permutation_matrix<T, X>::apply_from_right(std::vector<T> & w) {
#ifdef LEAN_DEBUG
    // dense_matrix<T, X> deb(*this);
    // T * deb_w = clone_vector<T>(w, row_count());
    // deb.apply_from_right(deb_w);
#endif
    std::vector<T> t(size());
    for (unsigned i = 0; i < size(); i++) {
        t[i] = w[m_rev[i]];
    }

    for (unsigned i = 0; i < size(); i++) {
        w[i] = t[i];
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
    // delete [] deb_w;
#endif
}

template <typename T, typename X> template <typename L>
void permutation_matrix<T, X>::copy_aside(std::vector<L> & t, std::vector<unsigned> & tmp_index, indexed_vector<L> & w) {
    for (unsigned i = t.size(); i > 0;) {
        i--;
        unsigned j = w.m_index[i];
        t[i] = w[j]; // copy aside all non-zeroes
        tmp_index[i] = j; // and the indices too
    }
}

template <typename T, typename X> template <typename L>
void permutation_matrix<T, X>::clear_data(indexed_vector<L> & w) {
    // clear old non-zeroes
    for (unsigned i = w.m_index.size(); i > 0;) {
        i--;
        unsigned j = w.m_index[i];
        w[j] = zero_of_type<L>();
    }
}

template <typename T, typename X>template <typename L>
void permutation_matrix<T, X>::apply_reverse_from_left(indexed_vector<L> & w) {
    // the result will be w = p(-1) * w
#ifdef LEAN_DEBUG
    // dense_matrix<L, X> deb(get_reverse());
    // L * deb_w = clone_vector<L>(w.m_data, row_count());
    // deb.apply_from_left(deb_w);
#endif
    std::vector<L> t(w.m_index.size());
    std::vector<unsigned> tmp_index(w.m_index.size());

    copy_aside(t, tmp_index, w);
    clear_data(w);

    // set the new values
    for (unsigned i = t.size(); i > 0;) {
        i--;
        unsigned j = m_permutation[tmp_index[i]];
        w[j] = t[i];
        w.m_index[i] = j;
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<L>(deb_w, w.m_data, row_count()));
    // delete [] deb_w;
#endif
}

template <typename T, typename X>template <typename L>
void permutation_matrix<T, X>::apply_reverse_from_left(std::vector<L> & w) {
    // the result will be w = p(-1) * w
#ifdef LEAN_DEBUG
    // dense_matrix<T, X> deb(get_reverse());
    // T * deb_w = clone_vector<T>(w, row_count());
    // deb.apply_from_left(deb_w);
#endif
    std::vector<L> t(size());
    unsigned i = size();
    while (i-- > 0) {
        t[m_permutation[i]] = w[i];
    }
    i = size();
    while (i-- > 0) {
        w[i] = t[i];
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
    // delete [] deb_w;
#endif
}
template <typename T, typename X>template <typename L>
void permutation_matrix<T, X>::apply_reverse_from_right(std::vector<L> & w) {
    // the result will be w = w * p(-1)
#ifdef LEAN_DEBUG
    // dense_matrix<T, X> deb(get_reverse());
    // T * deb_w = clone_vector<T>(w, row_count());
    // deb.apply_from_right(deb_w);
#endif
    std::vector<L>  t(size());
    unsigned i = size();
    while (i-- > 0) {
        t[i] = w[m_permutation[i]];
    }
    i = size();
    while (i-- > 0) {
        w[i] = t[i];
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
    // delete deb_w;
#endif
}

template <typename T, typename X> void permutation_matrix<T, X>::transpose_from_left(unsigned i, unsigned j) {
    // the result will be this = (i,j)*this
    lean_assert(i < size() && j < size() && i != j);
    auto pi = m_rev[i];
    auto pj = m_rev[j];
    set_val(pi, j);
    set_val(pj, i);
}

template <typename T, typename X> void permutation_matrix<T, X>::transpose_from_right(unsigned i, unsigned j) {
    // the result will be this = this * (i,j)
    lean_assert(i < size() && j < size() && i != j);
    auto pi = m_permutation[i];
    auto pj = m_permutation[j];
    set_val(i, pj);
    set_val(j, pi);
}

template <typename T, typename X>  unsigned * permutation_matrix<T, X>::clone_m_permutation() {
    auto r = new unsigned[size()];
    for (int i = size() - 1; i >= 0; i--) {
        r[i] = m_permutation[i];
    }
    return r;
}

template <typename T, typename X> void permutation_matrix<T, X>::multiply_by_permutation_from_left(permutation_matrix<T, X> & p) {
    auto clone = clone_m_permutation();
    lean_assert(p.size() == size());
    unsigned i = size();
    while (i-- > 0) {
        set_val(i, clone[p[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
    }
    delete [] clone;
}

// this is multiplication in the matrix sense
template <typename T, typename X> void permutation_matrix<T, X>::multiply_by_permutation_from_right(permutation_matrix<T, X> & p) {
    auto clone = clone_m_permutation();
    lean_assert(p.size() == size());
    unsigned i = size();
    while (i-- > 0) {
        set_val(i, p[clone[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
    }
    delete [] clone;
}

template <typename T, typename X> void permutation_matrix<T, X>::multiply_by_reverse_from_right(permutation_matrix<T, X> & q){ // todo : condensed permutations ?
    auto clone = clone_m_permutation();
    // the result is this = this*q(-1)
    unsigned i = size();
    while (i-- > 0) {
        set_val(i, q.m_rev[clone[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
    }
    delete [] clone;
}

template <typename T, typename X> void permutation_matrix<T, X>::multiply_by_permutation_reverse_from_left(permutation_matrix<T, X> & r){ // todo : condensed permutations?
    // the result is this = r(-1)*this
    auto clone = clone_m_permutation();
    // the result is this = this*q(-1)
    unsigned i = size();
    while (i-- > 0) {
        set_val(i, clone[r.m_rev[i]]);
    }
    delete [] clone;
}


template <typename T, typename X> bool permutation_matrix<T, X>::is_identity() const {
    unsigned i = size();
    while (i-- > 0) {
        if (m_permutation[i] != i) {
            return false;
        }
    }
    return true;
}


#ifdef LEAN_DEBUG
template <typename T, typename X>
permutation_generator<T, X>::permutation_generator(unsigned n): m_n(n), m_current(n) {
    lean_assert(n > 0);
    if (n > 1) {
        m_lower = new permutation_generator(n - 1);
    } else {
        m_lower = nullptr;
    }

    m_last = 0;
}

template <typename T, typename X>
permutation_generator<T, X>::permutation_generator(const permutation_generator & o): m_n(o.m_n), m_done(o.m_done), m_current(o.m_current), m_last(o.m_last) {
    if (m_lower != nullptr) {
        m_lower = new permutation_generator(o.m_lower);
    } else {
        m_lower = nullptr;
    }
}

template <typename T, typename X> bool
permutation_generator<T, X>::move_next() {
    if (m_done) {
        return false;
    }

    if (m_lower == nullptr) {
        if (m_last == 0) {
            m_last++;
            return true;
        } else {
            m_done = true;
            return false;
        }
    } else {
        if (m_last < m_n && m_last > 0) {
            m_current[m_last - 1] = m_current[m_last];
            m_current[m_last] = m_n - 1;
            m_last++;
            return true;
        } else {
            if (m_lower -> move_next()) {
                auto lower_curr = m_lower -> current();
                for ( unsigned i = 1; i < m_n; i++ ){
                    m_current[i] = (*lower_curr)[i - 1];
                }
                m_current[0] = m_n - 1;
                m_last = 1;
                return true;
            } else {
                m_done = true;
                return false;
            }
        }
    }
}

template <typename T, typename X>
inline unsigned number_of_inversions(permutation_matrix<T, X> & p) {
    unsigned ret = 0;
    unsigned n = p.size();
    for (unsigned i = 0; i < n; i++) {
        for (unsigned j = i + 1; j < n; j++) {
            if (p[i] > p[j]) {
                ret++;
            }
        }
    }
    return ret;
}

template <typename T, typename X>
T det_val_on_perm(permutation_matrix<T, X>* u, const matrix<T, X>& m) {
    unsigned n = m.row_count();
    T ret = numeric_traits<T>::one();
    for (unsigned i = 0; i < n; i++) {
        unsigned j = (*u)[i];
        ret *=  m(i, j);
    }
    return ret * sign(*u);
}

template <typename T, typename X>
T determinant(const matrix<T, X>& m) {
    lean_assert(m.column_count() == m.row_count());
    unsigned n = m.row_count();
    permutation_generator<T, X> allp(n);
    T ret = numeric_traits<T>::zero();
    while (allp.move_next()){
        ret += det_val_on_perm(allp.current(), m);
    }
    return ret;
}
#endif
}
