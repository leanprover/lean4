/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/metavar.h"

namespace lean {
/**
   \brief Wrapper for metavar_env that only allows us to access the assignment.
*/
class assignment {
    metavar_env m_menv;
public:
    assignment(metavar_env const & menv):m_menv(menv) {}
    optional<expr> operator()(name const & mvar) const { return m_menv->get_subst(mvar); }
};
}
