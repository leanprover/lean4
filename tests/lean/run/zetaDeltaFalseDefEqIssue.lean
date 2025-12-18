import Lean

/--
info: true
true
-/
#guard_msgs in
open Lean Meta in
run_meta do
  withLetDecl `x (mkConst ``Nat) (mkNatLit 10) fun x => do
    IO.println (← isDefEq x x)
    withConfig (fun c => { c with zeta := false, zetaDelta := false }) do
      IO.println (← isDefEq x x) -- Should return `true` even if `zetaDelta := false`
      return ()
