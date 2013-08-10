/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "level.h"

namespace lean {
class environment;
/**
   \brief Object for managing the environment, parser, pretty printer,
   elaborator, etc.
*/
class frontend {
    struct imp;
    std::shared_ptr<imp> m_imp;
    explicit frontend(imp * new_ptr);
    explicit frontend(std::shared_ptr<imp> const & ptr);
public:
    frontend();
    ~frontend();

    // =======================================
    // Parent/Child frontend management
    /**
        \brief Create a child environment. This frontend object will
        only allow "read-only" operations until all children frontend
        objects are deleted.
    */
    frontend mk_child() const;

    /** \brief Return true iff this fronted has children frontend. */
    bool has_children() const;

    /** \brief Return true iff this frontend has a parent frontend. */
    bool has_parent() const;

    /** \brief Return parent frontend */
    frontend parent() const;
    // =======================================

    /** \brief Coercion frontend -> environment. */
    environment const & env() const;
    operator environment const &() const { return env(); }

    level add_uvar(name const & n, level const & l);
    level add_uvar(name const & n);
    level get_uvar(name const & n) const;


};
}
