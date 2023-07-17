/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

/-- An exception plus state monad transformer (ι.e., `ExceptT` + `StateT`). -/
abbrev EStateT.{u,v} (ε : Type u) (σ : Type u) (m : Type u → Type v) :=
  ExceptT ε <| StateT σ m

namespace EStateT
variable {ε : Type u} {σ : Type u} {m : Type u → Type v}

@[inline] def run (init : σ) (self : EStateT ε σ m α) : m (Except ε α × σ) :=
  ExceptT.run self |>.run init

@[inline] def run' [Functor m] (init : σ) (self : EStateT ε σ m α) : m (Except ε α) :=
  ExceptT.run self |>.run' init

end EStateT
