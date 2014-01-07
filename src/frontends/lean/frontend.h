/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <vector>
#include "kernel/environment.h"
#include "kernel/io_state.h"
#include "library/expr_pair.h"
#include "frontends/lean/operator_info.h"

namespace lean {
/**
   \brief Load kernel, nat and set pretty printer.
*/
io_state init_frontend(environment const & env, bool no_kernel = false);

/*
  \brief Load kernel, nat, int, real and set pretty printer.
  It is used for testing.
*/
io_state init_test_frontend(environment const & env);

/**
   @name Notation for parsing and pretty printing.
*/
/*@{*/
void add_infix(environment const & env, io_state const & ios, name const & opn, unsigned p, expr const & d);
void add_infixl(environment const & env, io_state const & ios, name const & opn, unsigned p, expr const & d);
void add_infixr(environment const & env, io_state const & ios, name const & opn, unsigned p, expr const & d);
void add_prefix(environment const & env, io_state const & ios, name const & opn, unsigned p, expr const & d);
void add_postfix(environment const & env, io_state const & ios, name const & opn, unsigned p, expr const & d);
void add_mixfixl(environment const & env, io_state const & ios, unsigned sz, name const * opns, unsigned precedence, expr const & d);
void add_mixfixr(environment const & env, io_state const & ios, unsigned sz, name const * opns, unsigned precedence, expr const & d);
void add_mixfixc(environment const & env, io_state const & ios, unsigned sz, name const * opns, unsigned precedence, expr const & d);
void add_mixfixo(environment const & env, io_state const & ios, unsigned sz, name const * opns, unsigned precedence, expr const & d);
inline void add_mixfixl(environment const & env, io_state const & ios, std::initializer_list<name> const & l, unsigned p, expr const & d) {
    add_mixfixl(env, ios, l.size(), l.begin(), p, d);
}
inline void add_mixfixr(environment const & env, io_state const & ios, std::initializer_list<name> const & l, unsigned p, expr const & d) {
    add_mixfixr(env, ios, l.size(), l.begin(), p, d);
}
inline void add_mixfixc(environment const & env, io_state const & ios, std::initializer_list<name> const & l, unsigned p, expr const & d) {
    add_mixfixc(env, ios, l.size(), l.begin(), p, d);
}
inline void add_mixfixo(environment const & env, io_state const & ios, std::initializer_list<name> const & l, unsigned p, expr const & d) {
    add_mixfixo(env, ios, l.size(), l.begin(), p, d);
}
/**
   \brief Return the operator (if one exists) that can appear at
   the beginning of a language construct.

   \remark If there isn't a nud operator starting with \c n, then
   return the null operator.

   \remark This is used for parsing.
*/
operator_info find_nud(ro_environment const & env, name const & n);
/**
   \brief Return the operator (if one exists) that can appear
   inside of a language construct.

   \remark If there isn't a led operator starting with \c n, then
   return the null operator.

   \remark This is used for parsing.
*/
operator_info find_led(ro_environment const & env, name const & n);
/**
    \brief Return the precedence (aka binding power) of the given name.
*/
optional<unsigned> get_lbp(ro_environment const & env, name const & n);
/**
   \brief Return the operator (if one exists) associated with the
   given expression.

   \remark If an operator is not associated with \c e, then
   return the null operator.

   \remark This is used for pretty printing.

   \remark If unicode is false, then only operators containing
   safe ASCII chars are considered.
*/
operator_info find_op_for(ro_environment const & env, expr const & e, bool unicode);
/*@}*/

/**
   @name Implicit arguments.
*/
/*@{*/
/**
   \brief Mark the given arguments of \c n as implicit.
   The bit-vector array specify the position of the implicit arguments.
*/
void mark_implicit_arguments(environment const & env, name const & n, unsigned sz, bool const * implicit);
void mark_implicit_arguments(environment const & env, name const & n, std::initializer_list<bool> const & l);
/**
    \brief Return true iff \c n has implicit arguments
*/
bool has_implicit_arguments(ro_environment const & env, name const & n);
/**
    \brief Return the position of the arguments that are implicit.
*/
std::vector<bool> const & get_implicit_arguments(ro_environment const & env, name const & n);
/**
   \brief Return the position of the arguments that are implicit.
   \remark If \c n is not a constant, then return the empty vector.
*/
std::vector<bool> const & get_implicit_arguments(ro_environment const & env, expr const & n);
/**
   \brief This frontend associates an definition with each
   definition (or postulate) that has implicit arguments. The
   additional definition has explicit arguments, and it is called
   n::explicit. The explicit version can be used when the Lean
   frontend can't figure out the value for the implicit
   arguments.
*/
name const & get_explicit_version(ro_environment const & env, name const & n);
/**
   \brief Return true iff \c n is the name of the "explicit"
   version of an object with implicit arguments
*/
bool is_explicit(ro_environment const & env, name const & n);
/*@}*/


/**
   @name Coercions

   We support a very basic form of coercion. It is an expression
   with type T1 -> T2. This expression can be used to convert
   an expression of type T1 into an expression of type T2 whenever
   T2 is expected, but T1 was provided.
*/
/*@{*/
/**
   \brief Add a new coercion to the frontend.
   It throws an exception if f does not have type T1 -> T2, or if there is already a
   coercion from T1 to T2.
*/
void add_coercion(environment const & env, expr const & f);
/**
   \brief Return true iff the given expression is a coercion. That is, it was added using
   \c add_coercion.
*/
bool is_coercion(ro_environment const & env, expr const & f);
/**
   \brief Return a coercion from given_type to expected_type if it exists.
*/
optional<expr> get_coercion(ro_environment const & env, expr const & from_type, expr const & to_type);
/**
   \brief Return the list of coercions for the given type.
   The result is a list of pairs (to_type, function).
*/
list<expr_pair> get_coercions(ro_environment const & env, expr const & from_type);
/*@}*/

/**
   @name Aliases
*/
/*@{*/
optional<expr> get_alias(ro_environment const & env, name const & n);
optional<list<name>> get_aliased(ro_environment const & env, expr const & e);
void add_alias(environment const & env, name const & n, expr const & e);
/*@}*/
}
