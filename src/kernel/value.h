/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/**
   \brief Base class for values that have a hierarchical attached to it.
*/
class named_value : public value {
    name m_name;
public:
    named_value(name const & n):m_name(n) {}
    virtual ~named_value() {}
    virtual name get_name() const { return m_name; }
};

/**
   \brief Base class for values that have a hierarchical name and a type
   attached to it.
*/
class const_value : public named_value {
    expr m_type;
public:
    const_value(name const & n, expr const & t):named_value(n), m_type(t) {}
    virtual ~const_value() {}
    virtual expr get_type() const { return m_type; }
};

/**
   \brief Base class for values that have a hierarchical name attached to it, and
   have type Type().
*/
class type_value : public named_value {
public:
    type_value(name const & n):named_value(n) {}
    virtual expr get_type() const { return Type(); }
};
}
