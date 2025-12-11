module
import Std.Do

/--
error: `grind` failed
case grind
σ : Type u
σs : List (Type u)
inst : GetTy σ σs
σ' : Type u
s : σ'
h : Std.Do.SVal.getThe σ s = Std.Do.SVal.getThe σ
⊢ False
-/
#guard_msgs in
open Std.Do.SVal in
example {σs : List (Type u)} [GetTy σ σs] (σ' : Type u) (s : σ') : getThe (σs := σ'::σs) σ s = getThe (σs := σs) σ → False := by
  grind -verbose
