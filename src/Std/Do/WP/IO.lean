/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.System.IO
public import Std.Do.WP.Monad

@[expose] public section

/-!
# Barebones `WP` instance for `IO`

This module defines a `WP` instance for `IO` without any synthetic model of the `IO.RealWorld` whatsoever.
This is useful for reasoning about `IO` programs when the precise result of a side-effect is irrelevant;
for example it can be used to reason about random number generation.
It is however inadequate for reasoning about, e.g., `IO.Ref`s.
-/

namespace Std.Do.IO.Bare

open Std.Do

/--
This is pretty much the instance for `EStateM` specialized to `σ = IO.RealWorld`.
However, `IO.RealWorld` is omitted in the `PredShape`.
-/
scoped instance instWP : WP (EIO ε) (.except ε .pure) where
  wp x := -- Could define as PredTrans.mkExcept (PredTrans.modifyGetM (fun s => pure (EStateM.Result.toExceptState (x s))))
    { apply := fun Q => match x () with
        | .ok a _rw => Q.1 a
        | .error e _rw => Q.2.1 e
      conjunctive := by
        intro _ _
        apply SPred.bientails.of_eq
        dsimp
        cases (x ()) <;> rfl
    }

instance instLawfulMonad : LawfulMonad (EIO ε) := inferInstanceAs (LawfulMonad (EStateM ε IO.RealWorld))
