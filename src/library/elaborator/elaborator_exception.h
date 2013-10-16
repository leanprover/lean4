/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "kernel/trace.h"

namespace lean {
/**
   \brief Elaborator and related components store the reason for
   failure in trace objects.
*/
class elaborator_exception : public exception {
    trace m_trace;
public:
    elaborator_exception(trace const & tr):m_trace(tr) {}
    virtual ~elaborator_exception() {}
    virtual char const * what() const noexcept { return "elaborator exception"; }
    trace const & get_trace() const { return m_trace; }
};


}
