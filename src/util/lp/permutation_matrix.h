/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include <algorithm>
#include "util/debug.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
#include <string>
#include "util/lp/sparse_vector.h"
#include "util/lp/indexed_vector.h"
#include "util/lp/lp_settings.h"
#include "util/lp/matrix.h"
#include "util/lp/tail_matrix.h"
namespace lean {
#ifdef LEAN_DEBUG
    inline bool is_even(int k) {  return (k/2)*2 == k; }
#endif

    template <typename T, typename X>
    class permutation_matrix
        : public tail_matrix<T, X> {
        std::vector<unsigned> m_permutation;
        std::vector<unsigned> m_rev;

        class ref {
            permutation_matrix & m_p;
            unsigned m_i;
        public:
            ref(permutation_matrix & m, unsigned i):m_p(m), m_i(i) {}

            ref & operator=(unsigned  v) { m_p.set_val(m_i, v); return *this; }

            ref & operator=(ref const & v) {
                m_p.set_val(m_i, v.m_p.m_permutation[v.m_i]);
                return *this;
            }
            operator unsigned & () const { return m_p.m_permutation[m_i]; }
        };

    public:
        permutation_matrix() {}
        permutation_matrix(unsigned length);

        permutation_matrix(unsigned length, std::vector<unsigned> const & values);
        // create a unit permutation of the given length
        void init(unsigned length);

        unsigned get_rev(unsigned i) { return m_rev[i]; }

#ifdef LEAN_DEBUG
        permutation_matrix get_inverse() const {
            return permutation_matrix(size(), m_rev);
        }
        void print(std::ostream & out) const;
#endif

        ref operator[](unsigned i) { return ref(*this, i); }

        unsigned operator[](unsigned i) const { return m_permutation[i]; }

        template <typename L>
        void apply_from_left_perm(std::vector<L> & w);

        void apply_from_left(std::vector<X> & w, lp_settings &) { apply_from_left_perm(w); }

        void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) { apply_from_left_perm(w, settings);  }


        template <typename L>
        void apply_from_left_perm(indexed_vector<L> & w, lp_settings &);


        void apply_from_right(std::vector<T> & w);

        template <typename L>
        void copy_aside(std::vector<L> & t, std::vector<unsigned> & tmp_index, indexed_vector<L> & w);

        template <typename L>
        void clear_data(indexed_vector<L> & w);

        template <typename L>
        void apply_reverse_from_left(indexed_vector<L> & w);

        template <typename L>
        void apply_reverse_from_left(std::vector<L> & w);
        template <typename L>
        void apply_reverse_from_right(std::vector<L> & w);

        void set_val(unsigned i, unsigned pi) {
            lean_assert(i < size() && pi < size());  m_permutation[i] = pi;  m_rev[pi] = i;  }

        void transpose_from_left(unsigned i, unsigned j);

        unsigned apply_reverse(unsigned i) const { return m_rev[i];  }

        void transpose_from_right(unsigned i, unsigned j);
#ifdef LEAN_DEBUG
        T get_elem(unsigned i, unsigned j) const{
            return m_permutation[i] == j? numeric_traits<T>::one() : numeric_traits<T>::zero();
        }
        unsigned row_count() const{ return size(); }
        unsigned column_count() const { return size(); }
        virtual void set_number_of_rows(unsigned /*m*/) { }
        virtual void set_number_of_columns(unsigned /*n*/) { }
#endif
        unsigned * clone_m_permutation();

        void multiply_by_permutation_from_left(permutation_matrix<T, X> & p);

        // this is multiplication in the matrix sense
        void multiply_by_permutation_from_right(permutation_matrix<T, X> & p);

        void multiply_by_reverse_from_right(permutation_matrix<T, X> & q);

        void multiply_by_permutation_reverse_from_left(permutation_matrix<T, X> & r);

        void shrink_by_one_identity();

        bool is_identity() const;

        unsigned size() const { return m_rev.size(); }

        unsigned * values() const { return m_permutation; }
    }; // end of the permutation class

#ifdef LEAN_DEBUG
        template <typename T, typename X>
        class permutation_generator {
        unsigned m_n;
        permutation_generator* m_lower;
        bool m_done = false;
        permutation_matrix<T, X> m_current;
        unsigned m_last;
    public:
        permutation_generator(unsigned n);
        permutation_generator(const permutation_generator & o);
        bool move_next();

        ~permutation_generator() {
        if (m_lower != nullptr) {
        delete m_lower;
    }
    }

    permutation_matrix<T, X> *current() {
        return &m_current;
    }
    };

        template <typename T, typename X>
        inline unsigned number_of_inversions(permutation_matrix<T, X> & p);

        template <typename T, typename X>
        int sign(permutation_matrix<T, X> & p) {
        return is_even(number_of_inversions(p))? 1: -1;
    }

        template <typename T, typename X>
        T det_val_on_perm(permutation_matrix<T, X>* u, const matrix<T, X>& m);

        template <typename T, typename X>
        T determinant(const matrix<T, X>& m);
#endif
    }
