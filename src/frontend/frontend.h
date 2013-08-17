/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "environment.h"
#include "operator_info.h"

namespace lean {
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
    environment const & get_environment() const;
    operator environment const &() const { return get_environment(); }

    level add_uvar(name const & n, level const & l);
    level add_uvar(name const & n);
    level get_uvar(name const & n) const;

    // =======================================
    // Notation
    void add_infixl(name const & opn, unsigned precedence, name const & n);
    void add_infixr(name const & opn, unsigned precedence, name const & n);
    void add_prefix(name const & opn, unsigned precedence, name const & n);
    void add_postfix(name const & opn, unsigned precedence, name const & n);
    void add_mixfixl(unsigned sz, name const * opns, unsigned precedence, name const & n);
    void add_mixfixr(unsigned sz, name const * opns, unsigned precedence, name const & n);
    void add_mixfixc(unsigned sz, name const * opns, unsigned precedence, name const & n);
    /**
        \brief Return the operator (if it exists) associated with the
        given internal name.

        \remark If an operator is not associated with \c n, then
        return the nil operator.
    */
    operator_info find_op_for(name const & n) const;
    // =======================================
};
}
