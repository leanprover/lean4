/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Quotient types for kernels with proof irrelevance.
*/
#pragma once
#include "kernel/normalizer_extension.h"
#include <vector>

namespace lean {
/** \brief Normalizer extension for applying quotient computational rules. */
class quotient_normalizer_extension : public normalizer_extension {
public:
    virtual optional<expr> operator()(expr const & e, abstract_type_context & ctx) const;
    virtual optional<expr> is_stuck(expr const & e, abstract_type_context & ctx) const;
    virtual bool supports(name const & feature) const;
    virtual bool is_recursor(environment const & env, name const & n) const;
    virtual bool is_builtin(environment const & env, name const & n) const;
};

/** \brief The following function must be invoked to register the quotient type computation rules in the kernel. */
environment declare_quotient(environment const & env);
/** \brief Return true iff \c n is one of the quotient type builtin constants. */
bool is_quotient_decl(environment const & env, name const & n);
/** \brief Return true iff the environment has a declared quotient type. */
bool has_quotient(environment const & env);
/** \brief Names of declarations that are required for the quotient extension. */
std::vector<name> quotient_required_decls();
void initialize_quotient_module();
void finalize_quotient_module();
}
