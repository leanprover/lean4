import Lean.Meta.Sym
open Lean Meta Sym

opaque p : Nat → Prop
opaque q : Nat → Nat → Prop

def ex := ∃ x : Nat, p x ∧ q x .zero

def test : SymM Unit := do
  let p ← mkPatternFromTheorem ``Exists.intro
  let e := (← getConstInfo ``ex).value!
  let some r ← p.match? e | throwError "failed"
  let app := mkAppN (mkConst ``Exists.intro r.us) r.args
  logInfo app
  for arg in r.args do
    if arg.isMVar then
      logInfo m!"{arg} : {← inferType arg}"
  return ()

/--
info: @Exists.intro Nat (fun x => And (p x) (q x Nat.zero)) ?m.1 ?m.2
---
info: ?m.1 : Nat
---
info: ?m.2 : (fun x => And (p x) (q x Nat.zero)) ?m.1
-/
#guard_msgs in
set_option pp.explicit true in
#eval SymM.run' test
