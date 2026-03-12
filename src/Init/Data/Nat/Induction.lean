/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.WF
meta import Init.MetaTypes
import Init.WFTactics

public section

@[expose] section

namespace Nat

/--
Strong induction on the natural numbers.

The induction hypothesis is that all numbers less than a given number satisfy the motive, which
should be demonstrated for the given number.
-/
@[elab_as_elim] protected def strongRecOn
    {motive : Nat → Sort u}
    (n : Nat)
    (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n :=
  ind n fun m _ ↦ Nat.strongRecOn m ind

/--
Case analysis based on strong induction for the natural numbers.
-/
@[elab_as_elim] protected def caseStrongRecOn
    {motive : Nat → Sort u}
    (a : Nat)
    (zero : motive 0)
    (ind : ∀ n, (∀ m, m ≤ n → motive m) → motive (n + 1)) : motive a :=
  Nat.strongRecOn a fun n ↦
    match n with
    | 0   => fun _  ↦ zero
    | n+1 => fun h₁ ↦ ind n (fun _ h₂ ↦ h₁ _ (lt_succ_of_le h₂))

end Nat
