/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "object.h"

namespace lean {
/**
    \brief Object for tracking coercion declarations.
    This object is mainly used for recording the declaration.
*/
class coercion_declaration : public neutral_object_cell {
    expr          m_coercion;
public:
    coercion_declaration(expr const & c):m_coercion(c) {}
    virtual ~coercion_declaration() {}
    virtual char const * keyword() const { return "Coercion"; }
    expr const & get_coercion() const { return m_coercion; }
};
}
