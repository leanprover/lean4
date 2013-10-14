/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
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
#include <algorithm>
namespace lean {
    using std::string;
    using std::endl;

    template <typename T>
    string T_to_string(const T & t) {
        //        return is_zero(t)?string(" "):string(".");
        std::ostringstream strs;
        strs << t;
        std::string str = strs.str();
        return str;
    }

    template <>
    string T_to_string(const int & t) {
        std::ostringstream strs;
        strs << t;
        std::string str = strs.str();
        return str;
    }
    template <>
    string T_to_string(const unsigned & t) {
        std::ostringstream strs;
        strs << t;
        std::string str = strs.str();
        return str;
    }


    string T_to_string(const mpq & t) {
        std::ostringstream strs;
        strs << t.get_double();
        std::string str = strs.str();
        return str;
    }

    template <typename T>
    bool val_is_smaller_than_eps(T const & t, double const & eps) {
        if (!numeric_traits<T>::precise()) {
            return numeric_traits<T>::get_double(t) < eps;
        }
        return t <= numeric_traits<T>::zero();
    }


    inline bool is_even(int k) {
        return (k/2)*2 == k;
    }

    template <typename T>
    bool vectors_are_equal(T * a, T *b, unsigned n) {
        double sum  = 0;
        double  max = 0;
        if (numeric_traits<T>::precise()) {
            for (unsigned i = 0; i < n; i ++){
                if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                    std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                    return false;
                }
            }
        } else {
            for (unsigned i = 0; i < n; i ++){
                double t = fabs(numeric_traits<T>::get_double(a[i] - b[i]));
                if (t > 0.000001) {
                    std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                    return false;
                }
                if (t > max) {
                    max = t;
                }
                sum += t;
            }
        }
        if (sum > 0.00001) {
            return false;
        }
        // cout << "vectors_are_equal :" << "sum = " << sum << ", max = " << max << endl;
        return true;
    }

    template <typename T>
    bool vectors_are_equal(T * a, std::vector<T>  &b, unsigned n) {
        if (numeric_traits<T>::precise()) {
            for (unsigned i = 0; i < n; i ++){
                if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                    std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                    return false;
                }
            }
        } else {
            for (unsigned i = 0; i < n; i ++){
                if (fabs(numeric_traits<T>::get_double(a[i] - b[i])) > 0.000001) {
                    std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                    return false;
                }
            }
        }
        return true;
    }

    template <typename T>
    bool vectors_are_equal(const std::vector<T> & a, const buffer<T>  &b) {
        unsigned n = a.size();
        if (n != b.size()) return false;
        if (numeric_traits<T>::precise()) {
            for (unsigned i = 0; i < n; i ++){
                if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                    std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                    return false;
                }
            }
        } else {
            for (unsigned i = 0; i < n; i ++){
                if (fabs(numeric_traits<T>::get_double(a[i] - b[i])) > 0.000001) {
                    std::cout << "a[" << i <<"] = " << a[i] << ", but " << "b[" << i <<"] = " << b[i] << std::endl;
                    return false;
                }
            }
        }
        return true;
    }
    template <typename T>
    bool vectors_are_equal(const std::vector<T> & a, const std::vector<T>  &b) {
        unsigned n = a.size();
        if (n != b.size()) return false;
        if (numeric_traits<T>::precise()) {
            for (unsigned i = 0; i < n; i ++){
                if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                    std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                    return false;
                }
            }
        } else {
            for (unsigned i = 0; i < n; i ++){
                if (fabs(numeric_traits<T>::get_double(a[i] - b[i])) > 0.000001) {
                    std::cout << "a[" << i <<"] = " << a[i] << ", but " << "b[" << i <<"] = " << b[i] << std::endl;
                    return false;
                }
            }
        }
        return true;
    }

    template <typename X>
    X max_abs_in_vector(vector<X>& t){
        X r(zero_of_type<X>());
        for (auto & v : t)
            r = std::max(abs(v) , r);
        return r;
    }

    template <typename X>
    X min_abs_in_vector(vector<X>& t){
        X r(zero_of_type<X>());
        for (auto & v : t) {
            if (is_zero(v)) continue;
            if (is_zero(r)) {
                r = abs(v);
            } else {
                r = std::min(abs(v) , r);
            }
        }
        return r;
    }

#ifndef NDEBUG
    // used for debugging purposes only
    template <typename T, typename X>
    class matrix {
    public:
        virtual T get_elem (unsigned i, unsigned j) const = 0;
        virtual unsigned row_count() const  = 0;
        virtual unsigned column_count() const = 0;
        virtual void set_number_of_rows(unsigned m)  = 0;
        virtual void set_number_of_columns(unsigned n) = 0;

        virtual ~matrix() {}

        bool is_equal(const matrix<T, X>& other) {
            if (other.row_count() != row_count() || other.column_count() != column_count())
                return false;
            lp_settings settings;
            for (unsigned i = 0; i < row_count(); i++) {
                for (unsigned j = 0; j < column_count(); j++) {
                    auto a = get_elem(i, j);
                    auto b = other.get_elem(i, j);
                    if (numeric_traits<T>::precise()) {
                        if (a != b) return false;
                    } else if (fabs(numeric_traits<T>::get_double(a - b)) > 0.000001) {
                        // cout << "returning false from operator== of matrix comparison" << endl;
                        // cout << "this matrix is " << endl;
                        // print_matrix(*this);
                        // cout << "other matrix is " << endl;
                        // print_matrix(other);
                        return false;
                    }
                }
            }
            return true;
        }
        bool operator == (matrix<T, X> const & other) {
            return is_equal(other);
        }
        T operator()(unsigned i, unsigned j) const { return get_elem(i, j); }
    };
#endif

    // These matrices appear at the end of the list
    template <typename T, typename X>
    class tail_matrix
#ifndef NDEBUG
        : public matrix<T, X>
#endif
    {
    public:
        virtual void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) = 0;
        virtual void apply_from_left(vector<X> & w, lp_settings & settings) = 0;
        virtual void apply_from_right(vector<T> & w) = 0;
        virtual ~tail_matrix() {}
    };

#ifndef NDEBUG
    template <typename T, typename X>
    void apply_to_vector(matrix<T, X> & m, T * w) {
        // here m is a square matrix
        unsigned dim = m.row_count();

        T * wc = new T[dim];

        for (unsigned i = 0; i < dim; i++) {
            wc[i] = w[i];
        }

        for (unsigned i = 0; i < dim; i++) {
            T t = numeric_traits<T>::zero();
            for (unsigned j = 0; j < dim; j++) {
                t += m(i, j) * wc[j];
            }
            w[i] = t;
        }
        delete [] wc;
    }


    // used for debugging purposes only
    template <typename T, typename X>
    class dense_matrix: public matrix<T, X> {
    public:
    struct ref {
        unsigned m_i;
        dense_matrix & m_s;
        ref(unsigned i, dense_matrix & s) :m_i(i * s.m_n), m_s(s){}
        T & operator[] (unsigned j) {
            return m_s.m_values[m_i + j];
        }
        const T & operator[] (unsigned j) const {
            return m_s.m_v[m_i + j];
        }
    };
        ref operator[] (unsigned i) {
            return ref(i, *this);
        }
        unsigned m_m; // number of rows
        unsigned m_n; // number of const
        T* m_values;//
        dense_matrix(unsigned m, unsigned n) : m_m(m), m_n(n) {
            m_values = new T[m * n];
            for (unsigned i = 0; i < m * n; i ++)
                m_values[i] = numeric_traits<T>::zero();
        }

        dense_matrix operator*=(matrix<T, X> const & a){
            lean_assert(column_count() == a.row_count());
            dense_matrix c(row_count(), a.column_count());
            for (unsigned i = 0; i < row_count(); i++) {
                for (unsigned j = 0; j < a.column_count(); j++) {
                    T v = numeric_traits<T>::zero();
                    for (unsigned k = 0; k < a.column_count(); k++) {
                        v += get_elem(i, k) * a(k, j);
                    }
                    c.set_elem(i, j, v);
                }
            }
            *this = c;
            return *this;
        }

        dense_matrix & operator=(matrix<T, X> const & other){
            if ( this == & other)
                return *this;
            m_values = new T[m_m * m_n];
            for (unsigned i = 0; i < m_m; i ++)
                for (unsigned j = 0; j < m_n; j++)
                    m_values[i * m_n + j] = other.get_elem(i, j);
            return *this;
        }

        dense_matrix & operator=(dense_matrix const & other){
            if ( this == & other)
                return *this;
            m_m = other.m_m;
            m_n = other.m_n;
            delete [] m_values;
            m_values = new T[m_m * m_n];
            for (unsigned i = 0; i < m_m; i ++)
                for (unsigned j = 0; j < m_n; j++)
                    m_values[i * m_n + j] = other.get_elem(i, j);
            return *this;
        }

        dense_matrix(dense_matrix<T, X> const & other) : m_m(other.row_count()), m_n(other.column_count()) {
            m_values = new T[m_m * m_n];
            for (unsigned i = 0; i < m_m; i ++)
                for (unsigned j = 0; j < m_n; j++)
                    m_values[i * m_n + j] = other.get_elem(i, j);
        }

        dense_matrix(matrix<T, X> const & other) :
            m_m(other.row_count()),
            m_n(other.column_count()) {
            m_values = new T[m_m * m_n];
            for (unsigned i = 0; i < m_m; i++)
                for (unsigned j = 0; j < m_n; j++)
                    m_values[i * m_n + j] = other.get_elem(i, j);
        }

        void apply_from_right(T * w) {
            T * t = new T[m_m];
            for (int i = 0; i < m_m; i ++) {
                T v = numeric_traits<T>::zero();
                for (int j = 0; j < m_m; j++) {
                    v += w[j]* get_elem(j, i);
                }
                t[i] = v;
            }

            for (int i = 0; i < m_m; i++) {
                w[i] = t[i];
            }
            delete [] t;
        }

        void apply_from_right(vector <T> & w) {
            T * t = new T[m_m];
            for (int i = 0; i < m_m; i ++) {
                T v = numeric_traits<T>::zero();
                for (int j = 0; j < m_m; j++) {
                    v += w[j]* get_elem(j, i);
                }
                t[i] = v;
            }

            for (int i = 0; i < m_m; i++) {
                w[i] = t[i];
            }
            delete [] t;
        }

        // void apply_from_right(indexed_vector<T> & w) {
        //     vector<T> t(w.m_index.size());
        //     vector<unsigned> tmp_index(w.m_index.size());
        //     copy_aside(t, tmp_index, w);
        //     clear_data(w);

        //     for (int i = 0; i < m_m; i ++) {
        //         T v = numeric_traits<T>::zero();
        //         for (int j = 0; j < m_m; j++) {
        //             v += w[j]* get_elem(j, i);
        //         }
        //         t[i] = v;
        //     }

        //     w.m_index.clear();
        //     for (int i = 0; i < m_m; i++) {
        //         w[i] = t[i];
        //         if (!numeric_traits<T>::is_zero(w[i])) {
        //             w.m_index.push_back(i);
        //         }
        //     }
        //     delete [] t;
        // }
        T * apply_from_left_with_different_dims(vector<T> &  w) {
            T * t = new T[m_m];
            for (int i = 0; i < m_m; i ++) {
                T v = numeric_traits<T>::zero();
                for (int j = 0; j < m_n; j++) {
                    v += w[j]* get_elem(i, j);
                }
                t[i] = v;
            }

            return t;
        }
        void apply_from_left(vector<T> & w , lp_settings & ) {
            apply_from_left(w);
        }

        void apply_from_left(vector<T> & w) {
            T * t = new T[m_m];
            for (int i = 0; i < m_m; i ++) {
                T v = numeric_traits<T>::zero();
                for (int j = 0; j < m_m; j++) {
                    v += w[j]* get_elem(i, j);
                }
                t[i] = v;
            }

            for (int i = 0; i < m_m; i ++) {
                w[i] = t[i];
            }
            delete [] t;
        }

        void apply_from_left(X * w, lp_settings & ) {
            T * t = new T[m_m];
            for (int i = 0; i < m_m; i ++) {
                T v = numeric_traits<T>::zero();
                for (int j = 0; j < m_m; j++) {
                    v += w[j]* get_elem(i, j);
                }
                t[i] = v;
            }

            for (int i = 0; i < m_m; i ++) {
                w[i] = t[i];
            }
            delete [] t;
        }

        void apply_from_left_to_X(vector<X> & w, lp_settings & ) {
            vector<X> t(m_m);
            for (int i = 0; i < m_m; i ++) {
                X v = zero_of_type<X>();
                for (int j = 0; j < m_m; j++) {
                    v += w[j]* get_elem(i, j);
                }
                t[i] = v;
            }

            for (int i = 0; i < m_m; i ++) {
                w[i] = t[i];
            }
        }

        virtual void set_number_of_rows(unsigned /*m*/) {}
        virtual void set_number_of_columns(unsigned /*n*/) { }

        T get_elem(unsigned i, unsigned j) const { return m_values[i * m_n + j]; }

        unsigned row_count() const { return m_m; }
        unsigned column_count() const { return m_n; }

        void set_elem(unsigned i, unsigned j, const T& val) {
            m_values[i * m_n + j] = val;
        }

        // This method pivots row i to row i0 by muliplying row i by
        //   alpha and adding it to row i0.
        void pivot_row_to_row(unsigned i, T alpha, unsigned i0,
                              double & pivot_epsilon) {
            thread_local T _0 = numeric_traits<T>::zero();
            for (unsigned j = 0; j < m_n; j++) {
                m_values[i0 * m_n + j] += m_values[i * m_n + j] * alpha;
                if (fabs(m_values[i0 + m_n + j]) < pivot_epsilon) {
                    m_values[i0 + m_n + j] = _0;
                }
            }
        }

        void swap_columns(unsigned a, unsigned b) {
            for (unsigned i = 0; i < m_m; i++) {
                T t = get_elem(i, a);
                set_elem(i, a, get_elem(i, b));
                set_elem(i, b, t);
            }
        }

        void swap_rows(unsigned a, unsigned b) {
            for (unsigned i = 0; i < m_n; i++) {
                T t = get_elem(a, i);
                set_elem(a, i, get_elem(b, i));
                set_elem(b, i, t);
            }
        }

        void multiply_row_by_constant(unsigned row, T & t) {
            for (unsigned i = 0; i < m_n; i++) {
                set_elem(row, i, t * get_elem(row, i));
            }
        }

        ~dense_matrix() {
            delete [] m_values;
        }
    };

    template <typename T, typename X>
    dense_matrix<T, X> operator* (matrix<T, X> & a, matrix<T, X> & b){
        dense_matrix<T, X> ret(a.row_count(), b.column_count());
        for (unsigned i = 0; i < ret.m_m; i++)
            for (unsigned j = 0; j< ret.m_n; j++) {
                T v = numeric_traits<T>::zero();
                for (unsigned k = 0; k < a.column_count(); k ++){
                    v += (a.get_elem(i, k) * b.get_elem(k, j));
                }
                ret.set_elem(i, j, v);
            }
        return  ret;
    }

    inline unsigned get_width_of_column(unsigned j, vector<vector<string>> & A) {
        unsigned r = 0;
        for (unsigned i = 0; i < A.size(); i++) {
            unsigned s = A[i][j].size();
            if (r < s) {
                r = s;
            }
        }
        return r;
    }
#endif
    inline void print_blanks(int n) {
        lean_assert(n >= 0);
        while (n--) {
            cout << ' ';
        }
    }
#ifndef NDEBUG
    inline void print_matrix_with_widths(vector<vector<string>> & A, vector<unsigned> & ws) {
        for (unsigned i = 0; i < A.size(); i++) {
            for (unsigned j = 0; j < A[i].size(); j++) {
                print_blanks(ws[j] - A[i][j].size());
                cout << A[i][j] << " ";
            }
            cout << endl;
        }
    }

    inline void print_string_matrix(vector<vector<string>> & A) {
        vector<unsigned> widths;

        for (unsigned j = 0; j < A[0].size(); j++) {
            widths.push_back(get_width_of_column(j, A));
        }

        print_matrix_with_widths(A, widths);
        std::cout << std::endl;
    }

    template <typename T, typename X>
    void print_matrix(matrix<T, X> const & m) {
        if (&m == nullptr) {
            std::cout << "null"  << std::endl;
            return;
        }
        vector<vector<string>> A(m.row_count());
        for (unsigned i = 0; i < m.row_count(); i++) {
            for (unsigned j = 0; j < m.column_count(); j++) {
                A[i].push_back(T_to_string(m.get_elem(i, j)));
            }
        }

        print_string_matrix(A);
    }


#endif

    template <typename T, typename X>
    class permutation_matrix
        : public tail_matrix<T, X> {
        unsigned m_length;
        vector<unsigned> m_permutation;
        vector<unsigned> m_rev;

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
        permutation_matrix() : m_length(0) {}
        permutation_matrix(unsigned length): m_length(length), m_permutation(length), m_rev(length) {
            unsigned i = m_length;
            while (i--)
                m_permutation[i] = m_rev[i] = i;
        }

        permutation_matrix(unsigned length, vector<unsigned> const & values): m_length(length), m_permutation(length), m_rev(length) {
            for (unsigned i = 0; i < length; i++) {
                set_val(i, values[i]);
            }
        }
        // create a unit permutation of the given length
        void init(unsigned length) {
            m_length = length;
            m_permutation.resize(length);
            m_rev.resize(length);
            unsigned i = length;
            while (i--)
                m_permutation[i] = m_rev[i] = i;
        }

        unsigned get_rev(unsigned i) {
            return m_rev[i];
        }

#ifndef NDEBUG
        permutation_matrix get_inverse() const {
            return permutation_matrix(m_length, m_rev);
        }
        void print() const {
            std::cout << "[";
            for (unsigned i = 0; i < m_length; i++) {
                std::cout << m_permutation[i];
                if (i < m_length - 1) {
                    std::cout << ",";
                } else {
                    std::cout << "]";
                }
            }
            std::cout << std::endl;
        }
#endif
        // void enlarge(unsigned delta) {
        //     unsigned len = m_length + delta;
        //     unsigned * np = new unsigned[len];
        //     unsigned * nr = new unsigned[len];
        //     memcpy(np, m_permutation, m_length*sizeof(unsigned));
        //     memcpy(nr, m_rev, m_length*sizeof(unsigned));
        //     unsigned i = m_length;
        //     m_length = len;
        //     delete [] m_permutation;
        //     delete [] m_rev;
        //     m_permutation = np;
        //     m_rev = nr;
        //     for (; i < len; i++) {
        //         set_val(i, i);
        //     }
        // }

        ref operator[](unsigned i) { return ref(*this, i); }

        unsigned operator[](unsigned i) const { return m_permutation[i]; }

        template <typename L>
        void apply_from_left_perm(vector<L> & w) {
#ifndef NDEBUG
            // dense_matrix<L, X> deb(*this);
            // L * deb_w = clone_vector<L>(w, row_count());
            // deb.apply_from_left(deb_w);
#endif
            L * t = new L[m_length];
            for (unsigned i = 0; i < m_length; i++) {
                t[i] = w[m_permutation[i]];
            }

            for (unsigned i = 0; i < m_length; i++) {
                w[i] = t[i];
            }
            delete [] t;
#ifndef NDEBUG
            // lean_assert(vectors_are_equal<L>(deb_w, w, row_count()));
            // delete [] deb_w;
#endif
        }

        void apply_from_left(vector<X> & w, lp_settings &) {
            apply_from_left_perm(w);
        }

        void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) {
            apply_from_left_perm(w, settings);
        }


        template <typename L>
        void apply_from_left_perm(indexed_vector<L> & w, lp_settings &) {
#ifndef NDEBUG
            // dense_matrix<T, L> deb(*this);
            // T * deb_w = clone_vector<T>(w.m_data, row_count());
            // deb.apply_from_right(deb_w);
#endif
            vector<L> t(w.m_index.size());
            vector<unsigned> tmp_index(w.m_index.size());
            copy_aside(t, tmp_index, w);
            clear_data(w);
            // set the new values
            for (unsigned i = t.size(); i > 0;) {
                i--;
                unsigned j = m_rev[tmp_index[i]];
                w[j] = t[i];
                w.m_index[i] = j;
            }
#ifndef NDEBUG
            // lean_assert(vectors_are_equal<T>(deb_w, w.m_data, row_count()));
            // delete [] deb_w;
#endif
        }


        void apply_from_right(vector<T> & w) {
#ifndef NDEBUG
            // dense_matrix<T, X> deb(*this);
            // T * deb_w = clone_vector<T>(w, row_count());
            // deb.apply_from_right(deb_w);
#endif
            T * t = new T[m_length];
            for (unsigned i = 0; i < m_length; i++) {
                t[i] = w[m_rev[i]];
            }

            for (unsigned i = 0; i < m_length; i++) {
                w[i] = t[i];
            }
            delete [] t;
#ifndef NDEBUG
            // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
            // delete [] deb_w;
#endif
        }

//         void apply_from_right(indexed_vector<T> & w) {
//             lean_assert(false); // i think it is never called
// #ifndef NDEBUG
//             // dense_matrix<T, X> deb(*this);
//             // T * deb_w = clone_vector<T>(w.m_data, row_count());
//             // deb.apply_from_right(deb_w);
// #endif
//             vector<T> t(w.m_index.size());
//             vector<unsigned> tmp_index(w.m_index.size());
//             copy_aside(t, tmp_index, w);
//             clear_data(w);
//             // set the new values
//             for (unsigned i = t.size(); i > 0;) {
//                 i--;
//                 unsigned j = m_permutation[tmp_index[i]];
//                 w[j] = t[i];
//                 w.m_index[i] = j;
//             }
//             for (unsigned i = 0; i < m_length; i++) {
//                 w[i] = t[i];
//             }
// #ifndef NDEBUG
//             // lean_assert(vectors_are_equal<T>(deb_w, w.m_data, row_count()));
//             // delete [] deb_w;
// #endif
//         }

        template <typename L>
        void copy_aside(vector<L> & t, vector<unsigned> & tmp_index, indexed_vector<L> & w) {
            for (unsigned i = t.size(); i > 0;) {
                i--;
                unsigned j = w.m_index[i];
                t[i] = w[j]; // copy aside all non-zeroes
                tmp_index[i] = j; // and the indices too
            }
        }

        template <typename L>
        void clear_data(indexed_vector<L> & w) {
            // clear old non-zeroes
            for (unsigned i = w.m_index.size(); i > 0;) {
                i--;
                unsigned j = w.m_index[i];
                w[j] = zero_of_type<L>();
            }
        }

        template <typename L>
        void apply_reverse_from_left(indexed_vector<L> & w) {
            // the result will be w = p(-1) * w
#ifndef NDEBUG
            // dense_matrix<L, X> deb(get_reverse());
            // L * deb_w = clone_vector<L>(w.m_data, row_count());
            // deb.apply_from_left(deb_w);
#endif
            vector<L> t(w.m_index.size());
            vector<unsigned> tmp_index(w.m_index.size());

            copy_aside(t, tmp_index, w);
            clear_data(w);

            // set the new values
            for (unsigned i = t.size(); i > 0;) {
                i--;
                unsigned j = m_permutation[tmp_index[i]];
                w[j] = t[i];
                w.m_index[i] = j;
            }
#ifndef NDEBUG
            // lean_assert(vectors_are_equal<L>(deb_w, w.m_data, row_count()));
            // delete [] deb_w;
#endif
        }

        template <typename L>
        void apply_reverse_from_left(std::vector<L> & w) {
            // the result will be w = p(-1) * w
#ifndef NDEBUG
            // dense_matrix<T, X> deb(get_reverse());
            // T * deb_w = clone_vector<T>(w, row_count());
            // deb.apply_from_left(deb_w);
#endif
            vector<L> t(m_length);
            for (unsigned i = 0; i < m_length; i++) {
                t[m_permutation[i]] = w[i];
            }

            for (unsigned i = 0; i < m_length; i++) {
                w[i] = t[i];
            }
#ifndef NDEBUG
            // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
            // delete [] deb_w;
#endif
        }
        template <typename L>
        void apply_reverse_from_right(vector<L> & w) {
            // the result will be w = w * p(-1)
#ifndef NDEBUG
            // dense_matrix<T, X> deb(get_reverse());
            // T * deb_w = clone_vector<T>(w, row_count());
            // deb.apply_from_right(deb_w);
#endif
            L * t = new T[m_length];
            for (unsigned i = 0; i < m_length; i++) {
                t[i] = w[m_permutation[i]];
            }

            for (unsigned i = 0; i < m_length; i++) {
                w[i] = t[i];
            }
            delete [] t;
#ifndef NDEBUG
            // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
            // delete deb_w;
#endif
        }

        void set_val(unsigned i, unsigned pi) {
            lean_assert(i < m_length && pi < m_length);
            m_permutation[i] = pi;
            m_rev[pi] = i;
        }

        void transpose_from_left(unsigned i, unsigned j) {
            // the result will be this = (i,j)*this
            lean_assert(i < m_length && j < m_length && i != j);
            auto pi = m_rev[i];
            auto pj = m_rev[j];
            set_val(pi, j);
            set_val(pj, i);
        }

        unsigned apply_reverse(unsigned i) const {
            return m_rev[i];
        }

        void transpose_from_right(unsigned i, unsigned j) {
            // the result will be this = this * (i,j)
            lean_assert(i < m_length && j < m_length && i != j);
            auto pi = m_permutation[i];
            auto pj = m_permutation[j];
            set_val(i, pj);
            set_val(j, pi);
        }
#ifndef NDEBUG
        T get_elem(unsigned i, unsigned j) const{
            return m_permutation[i] == j? numeric_traits<T>::one() : numeric_traits<T>::zero();
        }
        unsigned row_count() const{ return m_length; }
        unsigned column_count() const { return m_length; }
        virtual void set_number_of_rows(unsigned /*m*/) { }
        virtual void set_number_of_columns(unsigned /*n*/) { }
#endif

        unsigned * clone_m_permutation() {
            auto r = new unsigned[m_length];
            for (int i = m_length - 1; i >= 0; i--) {
                r[i] = m_permutation[i];
            }
            return r;
        }

        void multiply_by_permutation_from_left(permutation_matrix<T, X> & p) {
            auto clone = clone_m_permutation();
            lean_assert(p.m_length == m_length);
            for (unsigned i = 0; i < m_length; i++) {
                set_val(i, clone[p[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
            }
            delete clone;
        }

        // this is multiplication in the matrix sense
        void multiply_by_permutation_from_right(permutation_matrix<T, X> & p) {
            auto clone = clone_m_permutation();
            lean_assert(p.m_length == m_length);
            for (unsigned i = 0; i < m_length; i++) {
                set_val(i, p[clone[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
            }
            delete clone;
        }

        void multiply_by_reverse_from_right(permutation_matrix<T, X> & q){ // todo : condensed permutations ?
            auto clone = clone_m_permutation();
            // the result is this = this*q(-1)
            for (unsigned i = 0; i < m_length; i++) {
                set_val(i, q.m_rev[clone[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
            }
            delete clone;
        }

        void multiply_by_permutation_reverse_from_left(permutation_matrix<T, X> & r){ // todo : condensed permutations?
            // the result is this = r(-1)*this
            auto clone = clone_m_permutation();
            // the result is this = this*q(-1)
            for (unsigned i = 0; i < m_length; i++) {
                set_val(i, clone[r.m_rev[i]]);
            }
            delete clone;
        }

        void shrink_by_one_identity() {
            lean_assert(is_identity());
            m_length--;
            delete [] m_permutation;
            delete [] m_rev;
            m_permutation = new unsigned[m_length];
            m_rev = new unsigned[m_length];
            for (unsigned i = 0; i < m_length; i++) {
                m_permutation[i] = m_rev[i] = i;
            }
        }

        bool is_identity() const {
            for (unsigned i = 0; i < m_length; i++) {
                if (m_permutation[i] != i) {
                    return false;
                }
            }
            return true;
        }

        unsigned size() const { return m_length; }

        unsigned * values() const { return m_permutation; }
    }; // end of the permutation class

#ifndef NDEBUG
    template <typename T, typename X>
    class permutation_generator {
        unsigned m_n;
        permutation_generator* m_lower;
        bool m_done = false;
        permutation_matrix<T, X> m_current;
        unsigned m_last;
    public:
        permutation_generator(unsigned n): m_n(n), m_current(n) {
            lean_assert(n > 0);
            if (n > 1) {
                m_lower = new permutation_generator(n - 1);
            } else {
                m_lower = nullptr;
            }

            m_last = 0;
        }

        permutation_generator(const permutation_generator & o): m_n(o.m_n), m_done(o.m_done), m_current(o.m_current), m_last(o.m_last) {
            if (m_lower != nullptr) {
                m_lower = new permutation_generator(o.m_lower);
            } else {
                m_lower = nullptr;
            }
        }

        bool move_next() {
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
    int sign(permutation_matrix<T, X> & p) {
        return is_even(number_of_inversions(p))? 1: -1;
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
    // this matrix has ones on the diagonal, outside of a column
    // and one non-zero element off the diagonal in the column

    template <typename T, typename X>
    struct one_off_diagonal_matrix:
        public tail_matrix<T, X> {
        unsigned m_i; // the element row
        unsigned m_j; // the element column
        T m_val_jj; // the value in the column's diagonal element
        T m_val_ij; // the value off the diagonal element
    public:
        one_off_diagonal_matrix(unsigned i, unsigned j, T val_at_jj, T val_at_ij): m_i(i), m_j(j), m_val_jj(val_at_jj), m_val_ij(val_at_ij) {
        }

        one_off_diagonal_matrix(const one_off_diagonal_matrix<T, X> * o):m_i(o.m_i), m_j(o.m_j), m_val_jj(o.m_val_jj), m_val_ij(o.m_val_ij) {
#ifndef NDEBUG
            m_m = m_n = o.m_m;
#endif
        }

        void conjugate_by_permutation(permutation_matrix<T, X> & p) {
            // this = p * this * p(-1)
#ifndef NDEBUG
            // auto rev = p.get_reverse();
            // auto deb = ((*this) * rev);
            // deb = p * deb;
#endif
            m_j = p.get_rev(m_j);
            m_i = p.get_rev(m_i);
#ifndef NDEBUG
            // lean_assert(deb == *this);
#endif
        }
#ifndef NDEBUG
        unsigned m_m;
        unsigned m_n;
        virtual void set_number_of_rows(unsigned m) { m_n = m_m = m; }
        virtual void set_number_of_columns(unsigned n) {m_m = m_n = n; }

        T get_elem (unsigned i, unsigned j) const {
            if (j == m_j){
                if (i == m_j){
                    return 1 / m_val_jj;
                }
                if (i == m_i) {
                    return m_val_ij;
                }
                return numeric_traits<T>::zero();
            }

            return i == j ? numeric_traits<T>::one() : numeric_traits<T>::zero();
        }

        unsigned row_count() const { return m_m; } // not defined }
        unsigned column_count() const { return m_n; } // not defined  }
#endif
        void apply_from_left(vector<X> & w, lp_settings &) {
#ifndef NDEBUG
            // dense_matrix<T, X> deb(*this);
            // T * deb_w = clone_vector<T>(w, row_count());
            // deb.apply_from_left(deb_w);
#endif
            auto wj = w[m_j];
            w[m_j] =  wj / m_val_jj;
            w[m_i] += wj * m_val_ij;
#ifndef NDEBUG
            // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
            // delete deb_w;
#endif
        }

        template <typename L>
        void apply_from_left_local(indexed_vector<L> & w, lp_settings & settings) {
#ifndef NDEBUG
            // dense_matrix<T, X> deb(*this);
            // T * deb_w = clone_vector<T>(w.m_data, row_count());
            // deb.apply_from_left(deb_w);
#endif
            if (is_zero(w[m_j])) {
                return;
            }

            bool m_i_is_zero = is_zero(w[m_i]);
            L wj = w[m_j];
            w[m_j] =  wj / m_val_jj;
            if (m_i_is_zero) {
                w[m_i] = wj * m_val_ij;
                w.m_index.push_back(m_i);
            } else {
                w[m_i] += wj * m_val_ij; // we can get a zero here - do we need to check for it
            }

            lean_assert(check_vector_for_small_values(w, settings ));

#ifndef NDEBUG
            // lean_assert(vectors_are_equal<T>(deb_w, w.m_data, row_count()));
            // delete deb_w;
#endif
        }

        void apply_from_left_to_T(indexed_vector<T> &w, lp_settings &settings) {
            apply_from_left_local(w, settings);
        }
        void apply_from_right(vector<T> & w) {
#ifndef NDEBUG
            // dense_matrix<T, X> deb(*this);
            // T * deb_w = clone_vector<T>(w, row_count());
            // deb.apply_from_right(deb_w);
#endif
            w[m_j] = w[m_j] / m_val_jj + m_val_ij * w[m_i];
#ifndef NDEBUG
            // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
            // delete deb_w;
#endif
        }

//         void apply_from_right(indexed_vector<T> & w) {
// #ifndef NDEBUG
//             //        dense_matrix<T, X> deb(*this);
//             // vector<T> deb_w(w.m_data);
//             // deb.apply_from_right(deb_w);
// #endif
//             bool j_is_used = !numeric_traits<T>::is_zero(w[m_j]);
//             if (j_is_used) {
//                 w[m_j] = w[m_j] / m_val_jj + m_val_ij * w[m_i];
//             } else {
//                 w[m_j] = m_val_ij * w[m_i];
//                 w.m_index.push_back(m_j);
//             }
// #ifndef NDEBUG
//             // lean_assert(vectors_are_equal<T>(deb_w, w.m_data, row_count()));
//             // delete deb_w;
// #endif
//         }
    }; // end of one_off_diagonal_matrix

}
