/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include <unordered_map>
#include <string>
#include <algorithm>
#include "util/lp/lp_settings.h"
namespace lean {
template <typename T>
class column_info {
    std::string m_name;
    bool m_low_bound_is_set = false;
    bool m_low_bound_is_strict = false;
    bool m_upper_bound_is_set = false;
    bool m_upper_bound_is_strict = false;
    T m_low_bound;
    T m_upper_bound;
    T m_cost = numeric_traits<T>::zero();
    T m_fixed_value;
    bool m_is_fixed = false;

public:
    column_type get_column_type() const {
        return m_is_fixed? fixed : (m_low_bound_is_set? (m_upper_bound_is_set? boxed : low_bound) : (m_upper_bound_is_set? upper_bound: free_column));
    }

     column_type get_column_type_no_flipping() {
        if (m_is_fixed) {
            return column_type::fixed;
        }

        if (m_low_bound_is_set) {
            return m_upper_bound_is_set? boxed: low_bound;
        }
        // we are flipping the bounds!
        return m_upper_bound_is_set? upper_bound
            : free_column;
    }

    T get_low_bound() const {
        lean_assert(m_low_bound_is_set);
        return m_low_bound;
    }
    T get_upper_bound() const {
        lean_assert(m_upper_bound_is_set);
        return m_upper_bound;
    }

    bool low_bound_is_set() const {
        return m_low_bound_is_set;
    }

    bool upper_bound_is_set() const {
        return m_upper_bound_is_set;
    }

    T get_shift() {
        if (is_fixed()) {
            return m_fixed_value;
        }
        if (is_flipped()){
            return m_upper_bound;
        }
        return m_low_bound_is_set? m_low_bound : numeric_traits<T>::zero();
    }

    bool is_flipped() {
        return m_upper_bound_is_set && !m_low_bound_is_set;
    }

    bool adjusted_low_bound_is_set() {
        return !is_flipped()? low_bound_is_set(): upper_bound_is_set();
    }

    bool adjusted_upper_bound_is_set() {
        return !is_flipped()? upper_bound_is_set(): low_bound_is_set();
    }

    T  get_adjusted_upper_bound() {
        return get_upper_bound() - get_low_bound();
    }

    bool is_fixed() const {
        return m_is_fixed;
    }

    bool is_free() {
        return !m_low_bound_is_set && !m_upper_bound_is_set;
    }

    void set_fixed_value(T v) {
        m_is_fixed = true;
        m_fixed_value = v;
    }

    T get_fixed_value() const {
        lean_assert(m_is_fixed)
        return m_fixed_value;
    }

    T get_cost() const {
        return m_cost;
    }

    void set_cost(T const & cost) {
        m_cost = cost;
    }

    void set_name(std::string const & s) {
        m_name = s;
    }

    std::string get_name() const {
        return m_name;
    }

    void set_low_bound(T const & l) {
        m_low_bound = l;
        m_low_bound_is_set = true;
    }

    void set_upper_bound(T const & l) {
        m_upper_bound = l;
        m_upper_bound_is_set = true;
    }

    void unset_low_bound() {
        m_low_bound_is_set = false;
    }

    void unset_upper_bound() {
        m_upper_bound_is_set = false;
    }

    void unset_fixed() {
        m_is_fixed = false;
    }

    bool low_bound_holds(T v) {
        return !low_bound_is_set() || v >= m_low_bound -T(0.0000001);
    }

    bool upper_bound_holds(T v) {
        return !upper_bound_is_set() || v <= m_upper_bound + T(0.000001);
    }

    bool bounds_hold(T v) {
        return low_bound_holds(v) && upper_bound_holds(v);
    }

    bool adjusted_bounds_hold(T v) {
        return adjusted_low_bound_holds(v) && adjusted_upper_bound_holds(v);
    }

    bool adjusted_low_bound_holds(T v) {
        return !adjusted_low_bound_is_set() || v >= -T(0.0000001);
    }

    bool adjusted_upper_bound_holds(T v) {
        return !adjusted_upper_bound_is_set() || v <= get_adjusted_upper_bound() + T(0.000001);
    }
    bool is_infeasible() {
        return upper_bound_is_set() && low_bound_is_set() && get_upper_bound() < get_low_bound();
    }
    bool low_bound_is_strict() const {
        return m_low_bound_is_strict;
    }

    void set_low_bound_strict(bool val) {
        m_low_bound_is_strict = val;
    }

    bool upper_bound_is_strict() const {
        return m_upper_bound_is_strict;
    }

    void set_upper_bound_strict(bool val) {
        m_upper_bound_is_strict = val;
    }
};
}
