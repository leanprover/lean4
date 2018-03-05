/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

/* TODO(Leo): reduce after testing */
#define LEAN_AC_MACROS_TRUST_LEVEL 10000000

/* Remark: this module is currently used by tactic/smt/theory_ac.cpp.

   It provides infrastructure for:
   1- Representing AC applications `op a_1 (op a_2 ...)` more compactly using a macro `ac_macro op a_1 ... a_n`
   2- Helper functions for performing operations such as diff/append/lt/... on these terms.
   3- A macro for creating compact proofs for equalities of the form `(ac_macro op a_1 ... a_n) = (ac_macro op b_1 ... b_n)`
      where `[a_1, ..., a_n]` is a permutation of `[b_1, ..., b_n]`
   4- Helper class for detecting whether `op` is associative or commutative.

   TODO(Leo): move this class or implement a similar one in `library/` because the `ac_match`
   module needs this functionality. Here, we only need to keep the code for exposing this functionality
   as Lean tactics.

   TODO(Leo): the operations for creating and processing AC applications using the ac_app_macro
   sort arguments using is_hash_lt. This is ok for end-game tactics, but this is really bad
   for interactive tactics. It is bad even if we just sort and use is_hash_lt.
*/

namespace lean {
/*
   This helper class is used to "efficiently" decide whether `op` in an application `(op a b)` is
   associative/commutative or not. The type classes `is_associative` and `is_commutative` are parametrized
   by the operator `op`. We don't want to try to synthesize `is_associative _ op` and `is_commutative _ op`
   for each subterm `op a b`. In the current implementation we use a cache, mappings from `op` to
   the `optional<expr>` (`none` if there is no instance, and `some(inst)` if we manage to synthesize `inst`.

   This class does not yet use the `[algebra]` attribute to speedup the process.
   It does not use `get_class_attribute_symbols(env, "algebra")` to retrieve all symbols that
   appear in instances of type classes marked with the `algebra` attribute.
   The idea is the following, given `(op a b)`, if `get_app_fn(op)` is a constant, we can assume
   that `op` is not associative nor commutative if `const_name(get_app_fn(op))` is not in the set
   retrieved by `get_class_attribute_symbols`. This is an approximation because it does not take reduction into
   account, but it seems good enough in practice. Here is an example where this approach would fail: we have an
   AC operator `boo`, and we define
   ```
   @[reducible] def bla := boo
   ```
   `boo` is in the set returned by `get_class_attribute_symbols(env, "algebra")`, but `bla` is not.
   One possible workaround is to create an instance of "algebraic type" class using `bla`.
   We can even have a "fake" type class for this purpose.
   Another possibility is to tell users they should unfold `bla` in this kind of situation.
   The main question is: should we implement this optimization or not?

   Remark: we can also extend the optimization above to local constants. We create a set for local constants
   occurring in local instances of type classes tagged with the `[algebra]` attribute.

   Remark: for the ac_match module we also need to track the instances of the type class `is_symm_op`.
   For the future algebraic normalizer, we need to track many more instances.

   Summary: we need to move this module to `library/`, we need to extend it, and add missing optimizations.
*/
class ac_manager_old {
public:
    struct cache;
    typedef std::shared_ptr<cache> cache_ptr;
private:
    type_context_old & m_ctx;
    cache_ptr      m_cache_ptr;
public:
    ac_manager_old(type_context_old & ctx);
    ~ac_manager_old();
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
