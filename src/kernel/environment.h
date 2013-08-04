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
    std::shared_ptr<imp> m_imp;
    explicit environment(std::shared_ptr<imp> const & ptr);
    explicit environment(imp * new_ptr);
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

    /** \brief Display universal variables, and their constraints */
    void display_uvars(std::ostream & out) const;

    /**
       \brief Return universal variable with the given name.
       Throw an exception if variable is not defined in this environment.
    */
    level get_uvar(name const & n) const;

    /**
       \brief Create a child environment. This environment will only allow "read-only" operations until
       all children environments are deleted.
    */
    environment mk_child() const;

    /** \brief Return true iff this environment has children environments. */
    bool has_children() const;

    /** \brief Return true iff this environment has a parent environment. */
    bool has_parent() const;

    /**
        \brief Return parent environment of this environment.
        \pre has_parent()
    */
    environment parent() const;
};
}
