/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/annotation.h"

namespace lean {
/** \brief Annotate \c e with no-information generation.

    Whenever the elaborator finds this annotation it does not generate
    information for \c e or any subterm of \c e.
*/
expr mk_no_info(expr const & e);
/** \brief Return true iff \c e is a term annotated with mk_no_info */
bool is_no_info(expr const & e);
}
