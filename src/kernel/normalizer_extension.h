/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class abstract_type_context;

/**
   \brief The Lean kernel can be instantiated with different normalization extensions.
   Each extension is part of the trusted code base. The extensions allow us to support
   different flavors of the core type theory. We will use these extensions to implement
   inductive datatype (ala Coq), HIT, record types, etc.
*/
class normalizer_extension {
public:
    virtual ~normalizer_extension() {}
    virtual optional<expr> operator()(expr const & e, abstract_type_context & ctx) const = 0;
    /** \brief Return a non-none expression if the extension may reduce \c e after metavariables are instantiated.
        The expression returned is a meta-variable that if instantiated my allow the reduction to continue.
    */
    virtual optional<expr> is_stuck(expr const & e, abstract_type_context & ctx) const = 0;
    /** \brief Return true iff the extension supports a feature with the given name,
        this method is only used for sanity checking. */
    virtual bool supports(name const & feature) const = 0;
    virtual bool is_recursor(environment const & env, name const & n) const = 0;
    virtual bool is_builtin(environment const & env, name const & n) const = 0;
};

/** \brief Create the do-nothing normalizer extension */
std::unique_ptr<normalizer_extension> mk_id_normalizer_extension();

/** \brief Create the composition of two normalizer extensions */
std::unique_ptr<normalizer_extension> compose_ext(std::unique_ptr<normalizer_extension> && ext1, std::unique_ptr<normalizer_extension> && ext2);
}
