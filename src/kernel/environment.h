/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <memory>
#include "level.h"

namespace lean {
/**
   \brief Lean environment for defining constants, inductive
   datatypes, universe variables, et.c
*/
class environment {
    struct imp;
    std::unique_ptr<imp> m_imp;
public:
    environment();
    ~environment();

    /**
       \brief Define a new universe variable with name \c n and constraint <tt>n >= l</tt>.
       Return the new variable.

       \remark An exception is thrown if a universe inconsistency is detected.
    */
    level define_uvar(name const & n, level const & l);
    level define_uvar(name const & n) { return define_uvar(n, level()); }
    level define_uvar(char const * n, level const & l) { return define_uvar(name(n), l); }
    level define_uvar(char const * n) { return define_uvar(name(n), level()); }

    /**
       \brief Return true iff the constraint l1 >= l2 is implied by the constraints
       in the environment.
    */
    bool is_ge(level const & l1, level const & l2) const;

    void display_uvars(std::ostream & out) const;
};
}
