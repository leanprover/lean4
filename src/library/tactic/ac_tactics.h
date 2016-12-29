/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

/* TODO(Leo): reduce after testing */
#define LEAN_AC_MACROS_TRUST_LEVEL 10000000

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

expr mk_ac_app(expr const & op, buffer<expr> & args);
bool is_ac_app(expr const & e);
expr const & get_ac_app_op(expr const & e);
unsigned get_ac_app_num_args(expr const & e);
expr const * get_ac_app_args(expr const & e);
/* Return true iff e1 is a "subset" of e2.
   Example: The result is true for e1 := (a*a*a*b*d) and e2 := (a*a*a*a*b*b*c*d*d) */
bool is_ac_subset(expr const & e1, expr const & e2);
/* Store in r e1\e2.
   Example: given e1 := (a*a*a*a*b*b*c*d*d*d) and e2 := (a*a*a*b*b*d),
   the result is (a, c, d, d)

   \pre is_ac_subset(e2, e1) */
void ac_diff(expr const & e1, expr const & e2, buffer<expr> & r);
/* If e is an AC application for operator op, then copy its arguments to r.
   Otherwise, just copy e to r.

   Example: Given op := * and e := a*b*b*c, we append [a,b,b,c] to r.
   Example: Given op := + and e := a*b*b*c, we append [(a*b*b*c)] to r.
   Example: Given op := * and e := a,       we append [a] to r. */
void ac_append(expr const & op, expr const & e, buffer<expr> & r);
/* lexdeg order */
bool ac_lt(expr const & e1, expr const & e2);
/*
   Store the intersection of two AC terms in r.
   Example: Given (a*a*b*b*d) (a*b*b*c*c*d*d*d), we get (a, b, b, d) in r.

   \pre is_ac_app(e1) && is_ac_app(e2) */
void ac_intersection(expr const & e1, expr const & e2, buffer<expr> & r);
/* Create a flat AC application for e1 and e2.

   Example: op := *, (a*a*b*c) (a*c*c) ==> (a*a*a*c*b*c*c*c)
   Example: op := *, (a*a*b*c) a       ==> (a*a*a*b*c)
   Example: op := *, a         b       ==> (a*b)
*/
expr mk_ac_flat_app(expr const & op, expr const & e1, expr const & e2);

expr mk_perm_ac_macro(abstract_type_context & ctx, expr const & assoc, expr const & comm, expr const & e1, expr const & e2);

void initialize_ac_tactics();
void finalize_ac_tactics();
}
