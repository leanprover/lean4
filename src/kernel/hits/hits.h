/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Builtin HITs:
    - n-truncation
    - type quotients (non-truncated quotients)
*/
#pragma once

namespace lean {
/** \brief Normalizer extension for applying builtin HITs computational rules. */
class hits_normalizer_extension : public normalizer_extension {
public:
    virtual optional<pair<expr, constraint_seq>> operator()(expr const & e, extension_context & ctx) const;
    virtual optional<expr> is_stuck(expr const & e, extension_context & ctx) const;
    virtual bool supports(name const & feature) const;
};

/** \brief The following function must be invoked to register the builtin HITs computation rules in the kernel. */
environment declare_hits(environment const & env);
/** \brief Return true iff \c n is one of the HITs builtin constants. */
bool is_hits_decl(environment const & env, name const & n);
void initialize_hits_module();
void finalize_hits_module();
}
