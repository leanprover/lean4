/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/annotation.h"

// Auxiliary expression annotations for helping the generation
// of information for the info_manager

namespace lean {
/** \brief Annotate \c e with no-information generation.

    Whenever the elaborator finds this annotation it does not generate
    information for \c e or any subterm of \c e.
*/
expr mk_no_info(expr const & e);
/** \brief Return true iff \c e is a term annotated with mk_no_info */
bool is_no_info(expr const & e);

/** \brief Annotate \c e with "extra-info" annotation.
    It instructs elaborator to store the type of \c e.
*/
expr mk_extra_info(expr const & e, tag g);
expr mk_extra_info(expr const & e);
/** \brief Return true iff \c e is a term annotated with mk_extra_info */
bool is_extra_info(expr const & e);

/** \brief Annotate \c e with "notation-info" annotation.
    It instructs the elaborator to store the type of \c e.
    We use this feature to store the type of atomic notation (i.e.,
    notation without parameters).
*/
expr mk_notation_info(expr const & e, tag g);
expr mk_notation_info(expr const & e);
/** \brief Return true iff \c e is a term annotated with mk_notation_info */
bool is_notation_info(expr const & e);

void initialize_info_annotation();
void finalize_info_annotation();
}
