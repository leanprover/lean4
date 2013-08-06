/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {
/**
   \brief Return unit if <tt>num_args == 0<\tt>, args[0] if <tt>num_args == 1<\tt>, and
   <tt>(op args[0] (op args[1] (op ... )))<\tt>
*/
expr mk_bin_op(expr const & op, expr const & unit, unsigned num_args, expr const * args);
expr mk_bin_op(expr const & op, expr const & unit, std::initializer_list<expr> const & l);

/** \brief Return (Type m)  m >= bottom + Offset */
expr m_type();

/** \brief Return (Type u)  u >= m + Offset */
expr u_type();

/** \brief Return the Lean Boolean type. */
expr bool_type();
/** \brief Return true iff \c e is the Lean Boolean type. */
bool is_bool_type(expr const & e);

/** \brief Create a Lean Boolean value (true/false) */
expr bool_value(bool v);
/** \brief Return true iff \c e is a Lean Boolean value. */
bool is_bool_value(expr const & e);
/**
    \brief Convert a Lean Boolean value into a C++ Boolean value.
    \pre is_bool_value(e)
*/
bool to_bool(expr const & e);
/** \brief Return true iff \c e is the Lean true value. */
bool is_true(expr const & e);
/** \brief Return true iff \c e is the Lean false value. */
bool is_false(expr const & e);

/** \brief Return the Lean If-Then-Else operator. It has type: pi (A : Type), bool -> A -> A -> A */
expr if_fn();
/** \brief Return true iff \c e is the Lean If-Then-Else operator */
bool is_if_fn(expr const & e);

/** \brief Return the term (if A c t e) */
inline expr mk_if(expr const & A, expr const & c, expr const & t, expr const & e) { return app(if_fn(), A, c, t, e); }
/** \brief Return the term (if bool c t e) */
inline expr mk_bool_if(expr const & c, expr const & t, expr const & e) { return mk_if(bool_type(), c, t, e); }

/** \brief Return the Lean and operator */
expr and_fn();
/** \brief Return true iff \c e is the Lean and operator. */
bool is_and_fn(expr const & e);

/** \brief Return (and e1 e2) */
inline expr mk_and(expr const & e1, expr const & e2) { return app(and_fn(), e1, e2); }
inline expr mk_and(unsigned num_args, expr const * args) { return mk_bin_op(and_fn(), bool_value(true), num_args, args); }
inline expr mk_and(std::initializer_list<expr> const & l) { return mk_bin_op(and_fn(), bool_value(true), l); }

/** \brief Return the Lean or operator */
expr or_fn();
bool is_or_fn(expr const & e);

/** \brief Return (or e1 e2) */
inline expr mk_or(expr const & e1, expr const & e2) { return app(or_fn(), e1, e2); }
inline expr mk_or(unsigned num_args, expr const * args) { return mk_bin_op(or_fn(), bool_value(false), num_args, args); }
inline expr mk_or(std::initializer_list<expr> const & l) { return mk_bin_op(or_fn(), bool_value(false), l); }

/** \brief Return the Lean not operator */
expr not_fn();
bool is_not_fn(expr const & e);

/** \brief Return (not e) */
inline expr mk_not(expr const & e) { return app(not_fn(), e); }

/** \brief Return the Lean forall operator. It has type: <tt>Pi (A : Type), (A -> bool) -> Bool<\tt> */
expr forall_fn();
/** \brief Return true iff \c e is the Lean forall operator */
bool is_forall_fn(expr const & e);
/** \brief Return the term (forall A P), where A is a type and P : A -> bool */
inline expr mk_forall(expr const & A, expr const & P) { return app(forall_fn(), A, P); }

/** \brief Return the Lean exists operator. It has type: <tt>Pi (A : Type), (A -> Bool) -> Bool<\tt> */
expr exists_fn();
/** \brief Return true iff \c e is the Lean exists operator */
bool is_exists_fn(expr const & e);
/** \brief Return the term (exists A P), where A is a type and P : A -> bool */
inline expr mk_exists(expr const & A, expr const & P) { return app(exists_fn(), A, P); }

expr refl_fn();
bool is_refl_fn(expr const & e);
expr subst_fn();
bool is_subst_fn(expr const & e);
expr symm_fn();
bool is_symm_fn(expr const & e);
expr trans_fn();
bool is_trans_fn(expr const & e);
expr congr_fn();
bool is_congr_fn(expr const & e);
expr ext_fn();
bool is_ext_fn(expr const & e);
expr foralle_fn();
bool is_foralle_fn(expr const & e);
expr foralli_fn();
bool is_foralli_fn(expr const & e);
expr domain_inj_fn();
bool is_domain_inj_fn(expr const & e);
expr range_inj_fn();
bool is_range_inj_fn(expr const & e);

class environment;
/** \brief Initialize the environment with basic builtin declarations and axioms */
void add_basic_theory(environment & env);

/**
   \brief Helper macro for defining constants such as bool_type, int_type, int_add, etc.
*/
#define MK_BUILTIN(Name, ClassName)                                     \
expr Name() {                                                           \
    static thread_local expr r = to_expr(*(new ClassName()));           \
    return r;                                                           \
}                                                                       \
bool is_##Name(expr const & e) {                                        \
    return is_value(e) && to_value(e).kind() == ClassName::g_kind;      \
}

/**
   \brief Helper macro for generating "defined" constants.
*/
#define MK_CONSTANT(Name, NameObj)                              \
static name Name ## _name = NameObj;                            \
expr Name() {                                                   \
    static thread_local expr r = constant(Name ## _name);       \
    return r ;                                                  \
}                                                               \
bool is_##Name(expr const & e) {                                \
    return is_constant(e) && const_name(e) == Name ## _name;    \
}
}
