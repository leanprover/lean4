/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Quotient types for kernels with proof irrelevance.
*/
#pragma once

namespace lean {
/** \brief Normalizer extension for applying quotient computational rules. */
class quotient_normalizer_extension : public normalizer_extension {
public:
    virtual optional<pair<expr, constraint_seq>> operator()(expr const & e, extension_context & ctx) const;
    virtual optional<expr> is_stuck(expr const & e, extension_context & ctx) const;
    virtual bool supports(name const & feature) const;
};

/** \brief The following function must be invoked to register the quotient type computation rules in the kernel. */
environment declare_quotient(environment const & env);
/** \brief Return true iff \c n is one of the quotient type builtin constants. */
bool is_quotient_decl(environment const & env, name const & n);
void initialize_quotient_module();
void finalize_quotient_module();
}
