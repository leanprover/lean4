/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/util.h"

namespace lean {
class parser;

/** \brief Add alias id for the fully qualified name \c full_id. */
environment add_alias(parser & p, environment env, name const & id, name const & full_id,
                      levels const & ctx_levels, buffer<expr> const & ctx_params);

/** \brief Add an alias for the fully qualified name \c full_id.

    If composite is false, then the alias is the last part of \c full_id.
    Example:
        full_id == "foo.bla.mk"   ===>  alias is "mk"

    If composite is true, then the alias is the last *two* parts of \c full_id.
    Example:
        full_id == "foo.bla.mk"   ===>  alias is "bla.mk"

*/
environment add_alias(parser & p, environment env, bool composite,
                      name const & full_id, levels const & ctx_levels, buffer<expr> const & ctx_params);

implicit_infer_kind parse_implicit_infer_modifier(parser & p);
}
