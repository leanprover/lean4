/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/debug.h"
#include "util/buffer.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include <unordered_map>
#include <string>
#include <algorithm>
#include "util/lp/canonic_left_side.h"
namespace lean {
lconstraint_kind flip_kind(lconstraint_kind t) {
    return static_cast<lconstraint_kind>( - static_cast<int>(t));
}

std::string lconstraint_kind_string(lconstraint_kind t) {
    switch (t) {
    case LE: return std::string("<=");
    case LT: return std::string("<");
    case GE: return std::string(">=");
    case GT: return std::string(">");
    case EQ: return std::string("=");
    }
    lean_unreachable();
}

class lar_base_constraint {
public:
    lconstraint_kind m_kind;
    mpq m_right_side;
    virtual buffer<pair<mpq, var_index>> get_left_side_coefficients() const = 0;
    constraint_index m_index; // the index of constraint
    lar_base_constraint() {}
    lar_base_constraint(lconstraint_kind kind, mpq right_side, constraint_index index) :m_kind(kind), m_right_side(right_side), m_index(index) {}

    virtual unsigned size() const = 0;
    virtual ~lar_base_constraint(){}
};

class lar_constraint : public lar_base_constraint {
public:
    std::unordered_map<var_index, mpq> m_left_side;
    lar_constraint() {}
    lar_constraint(const buffer<pair<mpq, var_index>> & left_side, lconstraint_kind kind, mpq right_side, constraint_index index) :  lar_base_constraint(kind, right_side, index) {
        for (auto & it : left_side) {
            auto r = m_left_side.find(it.second);
            if (r == m_left_side.end()) {
                m_left_side[it.second] = it.first;
            } else {
                r->second += it.first;
            }
        }
    }

    lar_constraint(const lar_base_constraint & c): lar_base_constraint(c.m_kind, c.m_right_side, c.m_index) {
        for (auto t : c.get_left_side_coefficients())
            m_left_side.insert(std::make_pair(t.second, t.first));
    }

    unsigned size() const {
        return m_left_side.size();
    }

    buffer<pair<mpq, var_index>> get_left_side_coefficients() const {
        buffer<pair<mpq, var_index>> ret;
        for (auto it : m_left_side) {
            ret.push_back(std::make_pair(it.second, it.first));
        }
        return ret;
    }
};

class lar_normalized_constraint : public lar_base_constraint {
public:
    canonic_left_side* m_canonic_left_side;
    mpq m_ratio_to_original; // by multiplying this constraint by m_ratio_to_original we get the original one
    lar_constraint m_origin_constraint;
    lar_normalized_constraint(canonic_left_side * ls, mpq ratio, lconstraint_kind kind, mpq right_side, const lar_constraint & origin):
        lar_base_constraint(kind, right_side, origin.m_index),
        m_canonic_left_side(ls),
        m_ratio_to_original(ratio),
        m_origin_constraint(origin) {
    }

    lar_normalized_constraint() {}

    virtual buffer<pair<mpq, var_index>> get_left_side_coefficients() const {
        buffer<pair<mpq, var_index>> ret;
        for (auto t : m_canonic_left_side->m_coeffs) ret.push_back(t);
        return ret;
    }
    virtual unsigned size() const {
        return m_canonic_left_side->size();
    }
};
}
