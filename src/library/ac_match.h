/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once


/*
(Design notes)

The simplifier will be the main consumer of this module.
The simplifier will use AC matching for any simp lemma marked with the [ac_match] attribute.
If AC matching fails, we use the matching procedure provided by type_context_old.
The AC matching procedure implemented here does not subsume the matching procedure at type_context_old,
which performs matching modulo CIC reduction rules and has support for higher-order patterns.
By default, all simp lemmas derived from the local context will have the [ac_match] attribute.
The simplifier will have an option for disabling all AC matching support.

This module also has support for symmetric operators (see type class `is_symm_op`).
The `is_symm_op` type class subsumes `is_commutative` (commutative operators) and `is_symm` (symmetric relations)
type classes.

The AC matching procedure uses backtracking. The state is a tuple (Y, U, U_p, U_u, P, S, S_u) where
  - Y is a set of auxiliary temporary metavariables
  - U is a set of (unsolved) matching constraints: p =?= t, p may contain temporary metavariables, but t doesn't
  - U_p is a set of unsolved and postponed matching constraints. We use this set for storing matching constraints that should
    be solved using using type_context_old full force is_def_eq procedure.
  - U_u is a set of (unsolved) universe matching constraints: p =?= u, p may contain temporary universe metavariables, but u doesn't.
  - P (partial solutions) is a mapping from temporary metavariable to a triple (op, y, t) where
      op is an AC operator, y is in Y, and t is a term and the head of t is not op.
      moreover t does not contain temporary metavariables.
  - S (solutions) is a mapping from temporary metavariable to a term t. t does not contain
    temporary metavariables.
  - S_u (universe solutions) is a mapping from temporary universe metavariable to an universe term u.
    u does not contain temporary metavariables.

We implement the mappings P and S using arrays. We use a similar approach in type_context_old.
We implement U as a queue. The queue is an array and index qidx (queue head).
This module ignores the fact that the universe operator `max` is associative and commutative.
Non trival universe constraints are just postponed like in the type_context_old class.

This module does not use AC matching for implicit arguments. Matching constraints for implicit arguments
are stored at U_p. When U is empty, we just use full force type_context_old is_def_eq to process the constraints
at U_p. Note that the type_context_old must have access to S and S_u.
We address this requirement by using the type_context_old m_eassignment and m_uassignment
to implement S and S_u. Similarly, we use m_postponed to implement U_u.

Here are the rules for processing U elements

Remark: we use + and * to denote arbitrary AC operators

- ?x =?= s, S[?x] := s'
  ==>
  remove ?x =?= s from U IF is_def_eq(s, s')
  failure (i.e., backtrack) otherwise

  The is_def_eq is performed using the same "force" used in AC matching.
  Remark: s and s' do not contain temporary universe metavariables.
  Remark: S[?x] := s' denotes that s' is assigned to temporary metavariable ?x.

- ?x =?= s, P[?x] := (op, ?y, t)
  ==>
  failure IF head(s) is not op

- ?x =?= s_1 + ... + s_n,  P[?x] := (+, ?y, s')
  ==>
  replace with ?y =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n
  IF is_def_eq(s_k, s') for some s_k.
  failure otherwise

- ?x =?= s
  ==>
  remove ?x =?= s, and add S[?x] := s
  If ?x not in P nor S.

- t =?= s, t does not contain temporary metavariables
  ==>
  remove t =?= s IF is_def_eq(t, s)
  failure otherwise

- (f ...) =?= (g ...) and f different from g
  ==>
  replace with (f ...) =?= unfold_of (g ...) If unfold step is successful
  failure otherwise

- (f a_1 ... a_n) =?= (f b_1 ... b_n)
  ==>
  replace constaints with a_1 =?= b_1 ... a_n =?= b_n
  where a_i =?= b_i goes to U if explicit argument and to U_p otherwise

- (a_1 op a_2) =?= (b_1 op b_2) where op is not AC, but there is an instance of (is_sym_op _ _ op)
  ==>
  split
  1- replace with a_1 =?= b_1 and a_2 =?= b_2
  2- replace with a_1 =?= b_2 and a_2 =?= b_1

  We say this is the SYMM_OP_SPLIT rule, and it always creates two cases.

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, S[?x] := s, s is not a +-application
  ==>
  replace with t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n IF m <= n and is_def_eq(s, s_k)
  failure otherwise

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, S[?x] := s'_1 + ... + s'_n'
  ==>
  replace with t_2 + ... + t_m =?= s''_1 + ... + s''_n'' IF m - 1 <= n - n' and {s''_1, ..., s''_n'', s'_1, ... s'_n'} is definitionally equal to {s_1, ..., s_n}
  failure otherwise

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, P[?x] := (*, ?y, s) where * is not +.
  ==>
  If m <= n, split for each s_k s.t. s_k is of the form (s * s'_2' * ... * s'_n')
  replace with ?y =?= s'_2 * ...* s'_n' and t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n
  failure otherwise

  Remark: we don't need to perform a case split if (s_1 + ... + s_n) contains at most one term that is a *-application.

  We say this is an AC_P_SPLIT rule.

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, P[?x] := (+, ?y, s)
  ==>
  replace with ?y + t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n IF m < n and is_def_eq(s, s_k) for some s_k
  failure otherwise.

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, ?x is not in S nor P
  ==>
  For each s_k, we replace the constraint with
  - t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n and S[?x] := s_k IF m <= n
  - ?y + t_2 + .. + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n and P[?x] := (+, ?y, s_k) IF m < n where ?y is a fresh auxiliary temporary metavariable

  Remark: If m = n, then there are 2*n possible cases. If m < n, there are n cases.

  We say this is the AC_ASSIGN_SPLIT rule, and is the most expensive one.

- (g ...) + t_2 + ... + t_m =?= s_1 + ... + s_n,  `g` is not +
  ==>
  For each s_k with is a g-application
  - replace with (g ...) =?= s_k, t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n

  The number of cases is the number of g-applications at s_1 + ... + s_n

  We say this is the AC_APP_SPLIT rule

- (let x := t in p) =?= s
  ==>
  replace with p[x/t] =?= s

- p =?= (let x := t in s)
  ==>
  replace with p =?= s[x/t]

After we don't have more elements in U to process using the rules above, we process U_p and U_u constraints using type_context_old is_def_eq with full force.

Remark: in the rules above we do not have support for Pi and lambda-terms containing temporary metavariables.
We will treat macros and (A -> B) as applications. Here (A -> B) denotes a non dependent Pi-term.

*/
