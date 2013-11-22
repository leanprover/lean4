/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/exception.h"
#include "kernel/justification.h"

namespace lean {
/**
   \brief Tactic and related components store the reason for
   failure in justification objects.
*/
class tactic_exception : public exception {
    justification m_justification;
public:
    tactic_exception(justification const & j):m_justification(j) {}
    virtual ~tactic_exception() {}
    virtual char const * what() const noexcept { return "tactic exception"; }
    justification const & get_justification() const { return m_justification; }
};
}
