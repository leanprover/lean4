
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

#include <set>
#include "util/lp/lp_settings.h"
#include "util/lp/sparse_matrix.h"
#include "util/lp/sparse_vector.h"
#include "util/lp/pivot_chooser_base.h"


namespace lean {
    // following "Computing Sparse LU Factorizations for Large-Scale Linear Programming Bases", by Suhl, Suhl
template <typename T, typename X>
class suhl_pivot_chooser : public pivot_chooser_base {
// m_U is a square matrix
    sparse_matrix<T, X> & m_U;
    lp_settings const & m_settings;
public:
// constructor
    suhl_pivot_chooser(sparse_matrix<T, X> & U, lp_settings const & settings):  m_U(U), m_settings(settings) {
        lean_assert(U.row_count() == U.column_count());
    }

    bool get_column_singleton(unsigned * i, unsigned *j) {
        return m_U.find_column_singleton(i, j);
    }

    bool get_row_singleton(unsigned* i, unsigned *j) {
        return m_U.find_row_singleton(i, j);
    }

    void pivot_update_kernel(unsigned i, unsigned j) {
    }

    bool get_pivot_not_adjusted(unsigned *i, unsigned * j) {
        if (get_column_singleton(i, j)) {
            return true;
        }
        if (get_row_singleton(i, j)) {
            return true;
        }
        return m_U.get_non_singleton_pivot(i, j, m_settings.depth_of_rook_search, T(m_settings.c_partial_pivoting));
    }

    int get_pivot(unsigned i, unsigned * j) {
        if (get_pivot_not_adjusted(&i, j)) {
            *j = m_U.adjust_column_inverse(*j);
            return m_U.adjust_row_inverse(i);
        }
        return -1;
    }
};
}
