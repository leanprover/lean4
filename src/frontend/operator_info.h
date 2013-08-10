/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "name.h"

namespace lean {

/**
   \brief Operator fixity.
   Prefix:   ID _
   Infix:    _ ID _    (can be left or right associative)
   Postfix:  _ ID
   Mixfix_l: ID _ ID _ ... ID _
   Mixfix_r: _ ID _ ID ... _ ID
   Mixfix_c: ID _ ID _ ... ID _ ID
*/
enum class fixity { Prefix, Infix, Postfix, Mixfix_l, Mixfix_r, Mixfix_c };

enum class associativity { Left, Right };

class operator_info {
    struct imp;
    imp * m_ptr;
    explicit operator_info(imp * p);
public:
    operator_info(operator_info const & info);
    operator_info(operator_info && info);
    ~operator_info();

    operator_info & operator=(operator const & o);
    operator_info & operator=(operator&& o);

    operator_info infixl(name const & op, unsigned precedence);
    operator_info infixr(name const & op, unsigned precedence);
    operator_info prefix(name const & op, unsigned precedence);
    operator_info postfix(name const & op, unsigned precedence);
    operator_info mixfixl(unsigned num_parts, name const * parts, unsigned precedence);
    operator_info mixfixr(unsigned num_parts, name const * parts, unsigned precedence);
    operator_info mixfixc(unsigned num_parts, name const * parts, unsigned precedence);

    /** \brief Associate an internal name for this operator. */
    void add_internal_name(name const & n);

    /** \brief Return true iff the operator is overloaded. */
    bool is_overloaded() const;
    
    /** 
        \brief Return the list of internal names for this operator.
        The list has size greater than 1 iff the operator has been overloaded.
        When the operator is overloaded, the first internal name is
        the temporary name to be used during parsing (before elaboration).
    */
    list<name> const & get_internal_names() const;
    
    fixity get_fixity() const;
    
    associativity get_associativity() const;

    unsigned get_precedence() const;

    list<name> const & get_op_parts() const;
   
    operator_info copy() const;

    

#if 0    
    fixity        m_fixity;
    associativity m_assoc;  // Relevant only for infix operators.
    unsigned      m_precedence;
    list<name>    m_op_parts;  // operator parts, > 1 only if the operator is mixfix.
    list<name>    m_names;     // internal names, > 1 only if the operator is overloaded.
#endif
};

}
