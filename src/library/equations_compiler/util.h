/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/equations_compiler/equations.h"
namespace lean {
[[ noreturn ]] void throw_ill_formed_eqns();

bool get_eqn_compiler_zeta(options const & o);

/** \brief Helper class for modifying/updating an equations-expression.

    \remark The equations macro is awkward to use since it is a leftover
    from the Lean2 equation compiler. The class tries to hide the problems
    with this data-structure. We cannot change the equations-macro
    until we remove the old equations compiler.

    TODO(Leo): as soon as we remove the legacy code from Lean2, this
    class will be much simpler. */
class unpack_eqns {
    type_context_old::tmp_locals m_locals;
    expr                     m_src;
    buffer<expr>             m_fns;
    /* m_arity[i] contains the number of arguments for each equation lhs
       for m_fns[i].
       \remark m_arity.size() == m_fns.size().
       \remark The information stored in this field is ignore by repack. */
    buffer<unsigned>         m_arity;
    /* m_eqns[i] are the equations for m_fns[i].
       \remark m_eqs.size() == m_fns.size(). */
    buffer<buffer<expr>>     m_eqs;
public:
    /** \brief Extract the data stored in the equations-expression \c e.
        \pre is_equations(e) */
    unpack_eqns(type_context_old & ctx, expr const & e);
    /** \brief Re-build an equations-expression using the information
        stored at m_fns and m_eqs. */
    expr repack();

    /** Update the type of the function with the given idx.
        \remark The equations are not updated. They still reference the old function. */
    expr update_fn_type(unsigned fidx, expr const & type);

    unsigned get_num_fns() const { return m_fns.size(); }
    expr const & get_fn(unsigned fidx) const { return m_fns[fidx]; }
    buffer<expr> & get_eqns_of(unsigned fidx) { return m_eqs[fidx]; }
    buffer<expr> const & get_eqns_of(unsigned fidx) const { return m_eqs[fidx]; }
    unsigned get_arity_of(unsigned fidx) const { return m_arity[fidx]; }
};

/** \brief Helper class for unpacking a single equation nested in a equations expression. */
class unpack_eqn {
    expr                     m_src;
    type_context_old::tmp_locals m_locals;
    bool                     m_modified_vars{false};
    buffer<expr>             m_vars;
    expr                     m_nested_src;
    expr                     m_lhs;
    expr                     m_rhs;
    bool                     m_ignore_if_unused;
public:
    unpack_eqn(type_context_old & ctx, expr const & eqn);
    expr add_var(name const & n, expr const & type);
    buffer<expr> & get_vars() { return m_vars; }
    expr & lhs() { return m_lhs; }
    expr & rhs() { return m_rhs; }
    expr const & get_nested_src() const { return m_nested_src; }
    bool ignore_if_unused() const { return m_ignore_if_unused; }
    expr repack();
};

/** \brief Return true iff \c e is recursive. That is, some equation
    in the rhs has a reference to a function being defined by the
    equations. */
bool is_recursive_eqns(type_context_old & ctx, expr const & e);

expr erase_inaccessible_annotations(expr const & e);
list<expr> erase_inaccessible_annotations(list<expr> const & es);
bool has_inaccessible_annotation(expr const & e);
/* See comment at library/local_context.h */
local_context erase_inaccessible_annotations(local_context const & lctx);

void compile_aux_definition(environment & env, equations_header const & header, name const & user_name, name const & actual_name);

/* Create an auxiliary definition.

   Remark: `n` is the local name, and `actual_n` the kernel unique name.
   `n` and `actual_n` are different for scoped/private declarations.
*/
pair<environment, expr> mk_aux_definition(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx,
                                          equations_header const & header, name const & n, name const & actual_n, expr const & type, expr const & value);

/* Create an equation lemma #eqn_idx for f_name/f_actual_name. */
environment mk_equation_lemma(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx,
                              name const & f_name, name const & f_actual_name, unsigned eqn_idx, bool is_private,
                              buffer<expr> const & Hs, expr const & lhs, expr const & rhs);

/* Create an equational lemma for definition c based on its value.
   Example: Given
      def foo (x y : nat) := x + 10
   we create
      forall x y, foo x y = x + 10

   The proof is by reflexivity.

   This function is used to make sure we have equations for all definitions.


   Remark: `c` is the local name, and `c_actual` the kernel unique name.
   `c` and `c_actual` are different for scoped/private declarations.
*/
environment mk_simple_equation_lemma_for(environment const & env, options const & opts, bool is_private, name const & c, name const & c_actual, unsigned arity);

name mk_equation_name(name const & f_name, unsigned eqn_idx);

/* Return true iff e is a nat, int, char or string value. */
bool is_nat_int_char_string_name_value(type_context_old & ctx, expr const & e);

/* Given a variable (x : I A idx), where (I A idx) is an inductive datatype,
   for each constructor c of (I A idx), this function invokes fn(t, new_vars) where t is of the form (c A ...),
   where new_vars are fresh variables and are arguments of (c A ...)
   which have not been fixed by typing constraints. Moreover, fn is only invoked if
   the type of (c A ...) matches (I A idx). */
void for_each_compatible_constructor(type_context_old & ctx, expr const & var,
                                     std::function<void(expr const &, buffer<expr> &)> const & fn);

/* Given the telescope vars [x_1, ..., x_i, ..., x_n] and var := x_i,
   and t is a term containing variables t_vars := {y_1, ..., y_k} disjoint from {x_1, ..., x_n},
   Return [x_1, ..., x_{i-1}, y_1, ..., y_k, T(x_{i+1}), ..., T(x_n)},
   where T(x_j) updates the type of x_j (j > i) by replacing x_i with t.

   \remark The set of variables in t is a subset of {x_1, ..., x_{i-1}} union {y_1, ..., y_k}

   The output parameters from/to contain the replacement
   [x_i, ... x_n] => [t, T(x_{i+1}), ..., T(x_n)]

   The replacement will suppress entries x_j => T(x_j) if T(x_j) is equal to x_j.
*/
void update_telescope(type_context_old & ctx, buffer<expr> const & vars, expr const & var,
                      expr const & t, buffer<expr> const & t_vars,  buffer<expr> & new_vars,
                      buffer<expr> & from, buffer<expr> & to);

/* Create auxiliary definition for unfolding declaration `n`.
   See smart unfolding comment at type_context_old. */
environment mk_smart_unfolding_definition(environment const & env, options const & o, name const & n);

struct eqn_compiler_result {
    list<expr> m_fns;
    list<expr> m_counter_examples;
};

void initialize_eqn_compiler_util();
void finalize_eqn_compiler_util();
}
