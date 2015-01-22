/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/util.h"

namespace lean {
class parser;

/** \brief Helper class for parsing type declaration modifiers.

    \remark This used when parsing inductive and structure declarations.
*/
class type_modifiers {
    bool m_is_class;
public:
    type_modifiers():m_is_class(false) {}
    void parse(parser & p);
    bool is_class() const { return m_is_class; }
};

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

/**
   \brief Parse implicit parameter inference modifiers.

    Return implicit_infer_kind::None if next tokens are `(` `)`
    Return implicit_infer_kind::RelaxedImplicit if next tokens are `{` `}`
    Return implicit_infer_kind::Implicit, otherwise.
*/
implicit_infer_kind parse_implicit_infer_modifier(parser & p);
}
