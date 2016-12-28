/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
class ac_manager {
public:
    struct cache;
    typedef std::shared_ptr<cache> cache_ptr;
private:
    type_context & m_ctx;
    cache_ptr      m_cache_ptr;
public:
    ac_manager(type_context & ctx);
    ~ac_manager();
    /* If e is of the form (op a b), and op is associative (i.e., there is an instance (is_associative _ op)), then
       return proof term for forall x y z, op (op x y) z = op x (op y z) */
    optional<expr> is_assoc(expr const & e);
    /* If e is of the form (op a b), and op is commutative (i.e., there is an instance (is_commutative _ op)), then
       return proof term for forall x y, op x y = op y x */
    optional<expr> is_comm(expr const & e);
};

pair<expr, optional<expr>> flat_assoc(abstract_type_context & ctx, expr const & op, expr const & assoc, expr const & e);
/* Construct a proof that e1 = e2 modulo AC for the operator op. The proof uses the lemmas \c assoc and \c comm.
   It throws an exception if they are not equal modulo AC. */
expr perm_ac(abstract_type_context & ctx, expr const & op, expr const & assoc, expr const & comm, expr const & e1, expr const & e2);

void initialize_ac_tactics();
void finalize_ac_tactics();
}
