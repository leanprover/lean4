/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "name.h"
#include "list.h"
#include "format.h"

namespace lean {
/**
   \brief Operator fixity.
   Prefix:   ID _
   Infix:    _ ID _    (can be left or right associative)
   Postfix:  _ ID
   Mixfixl: ID _ ID _ ... ID _       (has at least two parts)
   Mixfixr: _ ID _ ID ... _ ID       (has at least two parts)
   Mixfixc: ID _ ID _ ... ID _ ID    (has at least two parts)
*/
enum class fixity { Prefix, Infix, Postfix, Mixfixl, Mixfixr, Mixfixc };

enum class associativity { Left, Right, None };

/**
   \brief Data-structure for storing user defined operator
   information. This information is used during parsing and
   pretty-printing.

*/
class operator_info {
    struct imp;
    imp * m_ptr;
    explicit operator_info(imp * p);
public:
    operator_info(operator_info const & info);
    operator_info(operator_info && info);
    ~operator_info();

    operator_info & operator=(operator_info const & o);
    operator_info & operator=(operator_info && o);

    friend void swap(operator_info & o1, operator_info & o2) { std::swap(o1.m_ptr, o2.m_ptr); }

    friend operator_info infixl(name const & op, unsigned precedence);
    friend operator_info infixr(name const & op, unsigned precedence);
    friend operator_info prefix(name const & op, unsigned precedence);
    friend operator_info postfix(name const & op, unsigned precedence);
    friend operator_info mixfixl(unsigned num_parts, name const * parts, unsigned precedence);
    friend operator_info mixfixr(unsigned num_parts, name const * parts, unsigned precedence);
    friend operator_info mixfixc(unsigned num_parts, name const * parts, unsigned precedence);

    /** \brief Associate an internal name for this operator. */
    void add_internal_name(name const & n);

    /** \brief Return true iff the operator is overloaded. */
    bool is_overloaded() const;

    /**
       \brief Return the list of internal names for this operator.
       The list has size greater than 1 iff the operator has been
       overloaded.
       Internal names are the real names used to identify the operator
       in the kernel.
    */
    list<name> const & get_internal_names() const;

    /** \brief Return the operator fixity. */
    fixity get_fixity() const;

    /** \brief Return the operator associativity. */
    associativity get_associativity() const;

    /** \brief Return the operator precedence. */
    unsigned get_precedence() const;

    /** \brief Return the operator name. For mixfix operators the result corresponds to the first part. */
    name const & get_op_name() const;

    /** \brief Return the operators parts. */
    list<name> const & get_op_name_parts() const;

    /** \brief Return a copy of the operator. */
    operator_info copy() const;
};
operator_info infixl(name const & op, unsigned precedence);
operator_info infixr(name const & op, unsigned precedence);
operator_info prefix(name const & op, unsigned precedence);
operator_info postfix(name const & op, unsigned precedence);
operator_info mixfixl(unsigned num_parts, name const * parts, unsigned precedence);
operator_info mixfixr(unsigned num_parts, name const * parts, unsigned precedence);
operator_info mixfixc(unsigned num_parts, name const * parts, unsigned precedence);
inline operator_info mixfixl(std::initializer_list<name> const & l, unsigned precedence) { return mixfixl(l.size(), l.begin(), precedence); }
inline operator_info mixfixr(std::initializer_list<name> const & l, unsigned precedence) { return mixfixr(l.size(), l.begin(), precedence); }
inline operator_info mixfixc(std::initializer_list<name> const & l, unsigned precedence) { return mixfixc(l.size(), l.begin(), precedence); }

format pp(operator_info const & o);
std::ostream & operator<<(std::ostream & out, operator_info const & o);
}
