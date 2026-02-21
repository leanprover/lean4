import Lean.Meta.Basic
/-!
# Tests of `pp.mdata`
-/

open Lean

set_option pp.mdata true

/-!
Having mdata on the head constant, partially applied, and fully applied.
-/
/--
info: ([mdata n:1 z:-1 b:true s:"str" x:_ m:foo.bar] @id) 3
---
info: ([mdata n:1 z:-1 b:true s:"str" x:_ m:foo.bar] id) 3
---
info: [mdata n:1 z:-1 b:true s:"str" x:_ m:foo.bar] id 3
-/
#guard_msgs in
run_meta
  let d : KVMap := KVMap.empty
    |>.insert `n (1 : Nat)
    |>.insert `z (-1 : Int)
    |>.insert `b true
    |>.insert `s "str"
    |>.insert `x (Unhygienic.run `(1+1))
    |>.insert `m `foo.bar
  Lean.logInfo <| mkApp2 (.mdata d <| .const ``id [1]) (mkConst ``Nat) (.lit (.natVal 3))
  Lean.logInfo <| Expr.app (.mdata d <| Expr.app (.const ``id [1]) (mkConst ``Nat)) (.lit (.natVal 3))
  Lean.logInfo <| Expr.mdata d <| mkApp2 (.const ``id [1]) (mkConst ``Nat) (.lit (.natVal 3))

/-!
`noindex`
-/
/-- info: [mdata noindex:true] 2 : Nat -/
#guard_msgs in #check no_index 2

/-!
Metadata blocks unexpanders
-/
/-- info: ([mdata noindex:true] HAdd.hAdd) 2 3 : Nat -/
#guard_msgs in #check (no_index HAdd.hAdd) 2 3
/-- info: 2 + 3 : Nat -/
#guard_msgs in #check HAdd.hAdd 2 3

/-!
Metadata blocks dot notation, both in implicit and explicit mode
-/
/-- info: ([mdata noindex:true] Nat.add) x y : Nat -/
#guard_msgs in variable (x y : Nat) in #check (no_index Nat.add) x y
/-- info: x.add y : Nat -/
#guard_msgs in variable (x y : Nat) in #check Nat.add x y
/-- info: [mdata noindex:true] x.add y : Nat -/
#guard_msgs in variable (x y : Nat) in #check no_index (Nat.add x y)
section
set_option pp.explicit true
/-- info: ([mdata noindex:true] Nat.add) x y : Nat -/
#guard_msgs in variable (x y : Nat) in #check (no_index Nat.add) x y
/-- info: x.add y : Nat -/
#guard_msgs in variable (x y : Nat) in #check Nat.add x y
/-- info: [mdata noindex:true] x.add y : Nat -/
#guard_msgs in variable (x y : Nat) in #check no_index (Nat.add x y)
end
