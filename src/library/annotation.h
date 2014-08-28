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
    Use helper obect #register_annotation_fn.
*/
void register_annotation(name const & n);
/** \brief Helper object for declaring a new kind of annotation */
struct register_annotation_fn {
    register_annotation_fn(name const & kind) { register_annotation(kind); }
};

/** \brief Create an annotated expression with tag \c kind based on \c e.

    \pre \c kind must have been registered using #register_annotation.

    \remark Annotations have no real semantic meaning, but are useful for guiding pretty printer and/or automation.
*/
expr mk_annotation(name const & kind, expr const & e);
/** \brief Return true iff \c e was created using #mk_annotation. */
bool is_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_annotation, and has tag \c kind. */
bool is_annotation(expr const & e, name const & kind);
/** \brief Return the annotated expression, \c e must have been created using #mk_annotation.

    \post get_annotation_arg(mk_annotation(k, e)) == e
*/
expr const & get_annotation_arg(expr const & e);
/** \brief Return the king of the annotated expression, \c e must have been created using #mk_annotation.

    \post get_annotation_arg(mk_annotation(k, e)) == k
*/
name const & get_annotation_kind(expr const & e);

/** \brief Tag \c e as a 'let value'-expression. 'let value' is a pre-registered annotation. */
expr mk_let_value_annotation(expr const & e);
/** \brief Tag \c e as a 'have'-expression. 'have' is a pre-registered annotation. */
expr mk_have_annotation(expr const & e);
/** \brief Tag \c e as a 'show'-expression. 'show' is a pre-registered annotation. */
expr mk_show_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_let_value_annotation. */
bool is_let_value_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_have_annotation. */
bool is_have_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_show_annotation. */
bool is_show_annotation(expr const & e);

/** \brief Return the serialization 'opcode' for annotation macros. */
std::string const & get_annotation_opcode();
}
