/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/expr.h"

namespace lean {
/** \brief Declare a new kind of annotation. It must only be invoked at startup time
    Use helper object #register_annotation_fn. */
void register_annotation(name const & n);

/** \brief Create an annotated expression with tag \c kind based on \c e.

    \pre \c kind must have been registered using #register_annotation.

    \remark Annotations have no real semantic meaning, but are useful for guiding pretty printer and/or automation.
*/
expr mk_annotation(name const & kind, expr const & e);
/** \brief Return true iff \c e was created using #mk_annotation. */
optional<expr> is_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_annotation, and has tag \c kind. */
bool is_annotation(expr const & e, name const & kind);
/** \brief Return true iff \c e is of the form (a_1 ... (a_k e') ...)
    where all a_i's are annotations and one of the is \c kind.

    \remark is_nested_annotation(e, kind) implies is_annotation(e, kind)
*/
bool is_nested_annotation(expr const & e, name const & kind);

/** \brief Return the annotated expression, \c e must have been created using #mk_annotation.

    \post get_annotation_arg(mk_annotation(k, e)) == e
*/
expr const & get_annotation_arg(expr const & e);
/** \brief Return the king of the annotated expression, \c e must have been created using #mk_annotation.

    \post get_annotation_arg(mk_annotation(k, e)) == k
*/
name get_annotation_kind(expr const & e);

/** \brief Return the nested annotated expression, \c e must have been created using #mk_annotation.
    This function is the "transitive" version of #get_annotation_arg.
    It guarantees that the result does not satisfy the predicate is_annotation.
*/
expr const & get_nested_annotation_arg(expr const & e);

/** \brief Copy annotation from \c from to \c to. */
expr copy_annotations(expr const & from, expr const & to);

/** \brief Tag \c e as a 'have'-expression. 'have' is a pre-registered annotation. */
expr mk_have_annotation(expr const & e);
/** \brief Tag \c e as a 'show'-expression. 'show' is a pre-registered annotation. */
expr mk_show_annotation(expr const & e);
/** \brief Tag \c e as a 'suffices'-expression. 'suffices' is a pre-registered annotation. */
expr mk_suffices_annotation(expr const & e);

expr mk_checkpoint_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_have_annotation. */
bool is_have_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_show_annotation. */
bool is_show_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_suffices_annotation. */
bool is_suffices_annotation(expr const & e);
bool is_checkpoint_annotation(expr const & e);

/** \brief Return the serialization 'opcode' for annotation macros. */
std::string const & get_annotation_opcode();

void initialize_annotation();
void finalize_annotation();
}
