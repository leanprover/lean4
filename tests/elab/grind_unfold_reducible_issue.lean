module
import Std.Do

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
open Std.Do.SVal in
example {σs : List (Type u)} [GetTy σ σs] (σ' : Type u) (s : σ') : getThe (σs := σ'::σs) σ s = getThe (σs := σs) σ → False := by
  grind -verbose
