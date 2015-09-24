/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_INDUCTIVE_H
#define _LEAN_INDUCTIVE_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Inductive datatypes API
*/
/*@{*/

LEAN_DEFINE_TYPE(lean_inductive_type);
LEAN_DEFINE_TYPE(lean_list_inductive_type);
LEAN_DEFINE_TYPE(lean_inductive_decl);

/** \brief Create a new inductive type with name \c n, type \c t, and constructors (aka introduction rules \c cs)
    \remark \c cs must be a list of local constants.
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_inductive_type_mk(lean_name n, lean_expr t, lean_list_expr cs, lean_inductive_type * r, lean_exception * ex);
/** \brief Dispose/delete the given inductive type */
void lean_inductive_type_del(lean_inductive_type t);

/** \brief Return the name of the recursor (aka eliminator) associated with an inductive type name \c n */
lean_bool lean_get_recursor_name(lean_name n, lean_name * r, lean_exception * ex);

/** \brief Store in \c r the name of the given inductive type. */
lean_bool lean_inductive_type_get_name(lean_inductive_type t, lean_name * r, lean_exception * ex);
/** \brief Store in \c r the type of the given inductive type. */
lean_bool lean_inductive_type_get_type(lean_inductive_type t, lean_expr * r, lean_exception * ex);
/** \brief Store in \c r the list of constructors of the given inductive type. */
lean_bool lean_inductive_type_get_constructors(lean_inductive_type t, lean_list_expr * r, lean_exception * ex);

/** \brief Create the empty list of inductive_types */
lean_bool lean_list_inductive_type_mk_nil(lean_list_inductive_type * r, lean_exception * ex);
/** \brief Create the list <tt>h :: t</tt> */
lean_bool lean_list_inductive_type_mk_cons(lean_inductive_type h, lean_list_inductive_type t, lean_list_inductive_type * r, lean_exception * ex);
/** \brief Delete/dispose the given list of inductive_types */
void lean_list_inductive_type_del(lean_list_inductive_type l);
/** \brief Return true iff the list is a "cons" (i.e., it is not the nil list) */
lean_bool lean_list_inductive_type_is_cons(lean_list_inductive_type l);
/** \brief Return true in \c b iff the two given lists are equal */
lean_bool lean_list_inductive_type_eq(lean_list_inductive_type l1, lean_list_inductive_type l2, lean_bool * b, lean_exception * ex);
/** \brief Store in \c r the head of the given list
    \pre lean_list_inductive_type_is_cons(l)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_list_inductive_type_head(lean_list_inductive_type l, lean_inductive_type * r, lean_exception * ex);
/** \brief Store in \c r the tail of the given list
    \pre lean_list_inductive_type_is_cons(l)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_list_inductive_type_tail(lean_list_inductive_type l, lean_list_inductive_type * r, lean_exception * ex);

/** \brief Create a mutually recursive inductive datatype declaration with universe parameters \c ps,
    \c n parameters and the given inductive types.
    \remark The remaining inductive datatype arguments are treated as indices. */
lean_bool lean_inductive_decl_mk(lean_list_name ps, unsigned n, lean_list_inductive_type ts, lean_inductive_decl * r, lean_exception * ex);
/** \brief Delete/dispose the given inductive declaration */
void lean_inductive_decl_del(lean_inductive_decl d);

/** \brief Store in \c r the list of universe parameter names of the given inductive declaration. */
lean_bool lean_inductive_decl_get_univ_params(lean_inductive_decl d, lean_list_name * r, lean_exception * ex);
/** \brief Store in \c r the number of parameters of the given inductive declaration. */
lean_bool lean_inductive_decl_get_num_params(lean_inductive_decl d, unsigned * r, lean_exception * ex);
/** \brief Store in \c r the list of inductive types in the given inductive declaration. */
lean_bool lean_inductive_decl_get_types(lean_inductive_decl d, lean_list_inductive_type * r, lean_exception * ex);

/** \brief Add the inductive declaration \c d to the given environment */
lean_bool lean_env_add_inductive(lean_env env, lean_inductive_decl d, lean_env * r, lean_exception * ex);

/** \brief Return lean_true if \c n is the name of an inductive type in the given environment,
    and store the inductive declaration that it is part of in \c r. */
lean_bool lean_env_is_inductive_type(lean_env env, lean_name n, lean_inductive_decl * r, lean_exception * ex);

/** \brief Return lean_true if \c n is the name of a constructor in the given environment, and
    store the name of the associated inductive type in \c r. */
lean_bool lean_env_is_constructor(lean_env env, lean_name n, lean_name * r, lean_exception * ex);

/** \brief Return lean_true if \c n is the name of a recursor (aka eliminator) in the given environment, and
    store the name of the associated inductive type in \c r. */
lean_bool lean_env_is_recursor(lean_env env, lean_name n, lean_name * r, lean_exception * ex);

/** \brief Return lean_true if \c n is the name of an inductive type in the given environment, and
    store the number of indices in \c r. */
lean_bool lean_env_get_inductive_type_num_indices(lean_env env, lean_name n, unsigned * r, lean_exception * ex);
/** \brief Return lean_true if \c n is the name of an inductive type in the given environment, and
    store the number of minor premises in \c r. */
lean_bool lean_env_get_inductive_type_num_minor_premises(lean_env env, lean_name n, unsigned * r, lean_exception * ex);
/** \brief Return lean_true if \c n is the name of an inductive type in the given environment, and
    store the number of type formers in \c r. */
lean_bool lean_env_get_inductive_type_num_type_formers(lean_env env, lean_name n, unsigned * r, lean_exception * ex);
/** \brief Return lean_true if \c n is the name of an inductive type in the given environment, and
    store lean_true in \c r if the inductive type supports dependent elimination. */
lean_bool lean_env_get_inductive_type_has_dep_elim(lean_env env, lean_name n, lean_bool * r, lean_exception * ex);
/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
