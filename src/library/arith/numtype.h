/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "value.h"

namespace lean {
/** \brief Base class for numeric types */
class num_type_value : public type_value {
    name m_unicode;
public:
    num_type_value(name const & n, name const & u):type_value(n), m_unicode(u) {}
    virtual ~num_type_value() {}
    virtual name get_unicode_name() const { return m_unicode; }
};
}
