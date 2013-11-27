/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "kernel/justification.h"

namespace lean {
/**
   \brief Elaborator and related components store the reason for
   failure in justification objects.
*/
class elaborator_exception : public exception {
    justification m_justification;
public:
    elaborator_exception(justification const & j):m_justification(j) {}
    virtual ~elaborator_exception() {}
    virtual char const * what() const noexcept { return "elaborator exception"; }
    justification const & get_justification() const { return m_justification; }
    virtual exception * clone() const { return new elaborator_exception(m_justification); }
    virtual void rethrow() const { throw *this; }
};
}
