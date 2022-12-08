/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean.Elab.Term

/--
  Set `isDefEq` configuration for the elaborator.
  Note that we enable all approximations but `quasiPatternApprox`

  In Lean3 and Lean 4, we used to use the quasi-pattern approximation during elaboration.
  The example:
  ```
  def ex : StateT δ (StateT σ Id) σ :=
  monadLift (get : StateT σ Id σ)
  ```
  demonstrates why it produces counterintuitive behavior.
  We have the `Monad-lift` application:
  ```
  @monadLift ?m ?n ?c ?α (get : StateT σ id σ) : ?n ?α
  ```
  It produces the following unification problem when we process the expected type:
  ```
  ?n ?α =?= StateT δ (StateT σ id) σ
  ==> (approximate using first-order unification)
  ?n := StateT δ (StateT σ id)
  ?α := σ
  ```
  Then, we need to solve:
  ```
  ?m ?α =?= StateT σ id σ
  ==> instantiate metavars
  ?m σ =?= StateT σ id σ
  ==> (approximate since it is a quasi-pattern unification constraint)
  ?m := fun σ => StateT σ id σ
  ```
  Note that the constraint is not a Milner pattern because σ is in
  the local context of `?m`. We are ignoring the other possible solutions:
  ```
  ?m := fun σ' => StateT σ id σ
  ?m := fun σ' => StateT σ' id σ
  ?m := fun σ' => StateT σ id σ'
  ```

  We need the quasi-pattern approximation for elaborating recursor-like expressions (e.g., dependent `match with` expressions).

  If we had use first-order unification, then we would have produced
  the right answer: `?m := StateT σ id`

  Haskell would work on this example since it always uses
  first-order unification.
-/
def setElabConfig (cfg : Meta.Config) : Meta.Config :=
  { cfg with foApprox := true, ctxApprox := true, constApprox := false, quasiPatternApprox := false }


end Lean.Elab.Term
