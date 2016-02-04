/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/lp/indexed_vector.h"
#include "util/lp/matrix.h"
// These matrices appear at the end of the list

namespace lean {
template <typename T, typename X>
class tail_matrix
#ifdef LEAN_DEBUG
    : public matrix<T, X>
#endif
{
public:
    virtual void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) = 0;
    virtual void apply_from_left(std::vector<X> & w, lp_settings & settings) = 0;
    virtual void apply_from_right(std::vector<T> & w) = 0;
    virtual ~tail_matrix() {}
};
}
