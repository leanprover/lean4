/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "kernel/pos_info_provider.h"
#include "util/sexpr/options.h"
#include "library/io_state.h"

namespace lean {
/** \brief Auxiliary object for "inserting" delimiters for flycheck */
class flycheck_scope {
    std::ostream &  m_out;
    bool            m_flycheck;
public:
    flycheck_scope(std::ostream & out, options const & o, char const * kind);
    flycheck_scope(io_state const & ios, char const * kind):
        flycheck_scope(ios.get_regular_stream(), ios.get_options(), kind) {}
    ~flycheck_scope();
    bool enabled() const { return m_flycheck; }
};
}
