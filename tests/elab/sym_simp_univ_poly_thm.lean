import Lean

/-!
`Sym.Simp.mkTheoremFromDecl` must accept universe-polymorphic theorems whose conclusion is not
an equality (`↔`, `¬`, plain propositions). It used to fail with "incorrect number of universe
levels" because the proof constant was created without universe levels before being wrapped by
`eq_true`/`eq_false`/`propext`. Reported by Henrik Böving with `Foo.ext_iff` below.
-/

open Lean Meta Sym Simp

@[ext]
structure Foo (α : Type u) where
  x : α
  y : BitVec 8

/-- `↔` conclusion, the reported case. -/
theorem foo_ext_iff (a b : Foo α) : a = b ↔ a.x = b.x ∧ a.y = b.y := Foo.ext_iff

/-- `¬` conclusion. -/
theorem some_ne_none (a : α) : ¬ (some a = none) := nofun

axiom Q : {α : Sort u} → α → Prop

/-- Plain propositional conclusion. -/
axiom my_Q {α : Sort u} (a : α) : Q a

axiom a : Foo Nat
axiom b : Foo Nat
axiom n : Nat

def test (declName : Name) (e : Expr) : MetaM Unit := SymM.run do
  let thm ← mkTheoremFromDecl declName
  let e ← shareCommon e
  let r ← SimpM.run' (thm.rewrite e)
  match r with
  | .step e' proof _ _ =>
    check proof
    logInfo m!"step: {e'}"
  | _ => throwError "expected the rewrite to fire"

def fooNat : Expr := mkApp (mkConst ``Foo [0]) (mkConst ``Nat)

/-- info: step: a.x = b.x ∧ a.y = b.y -/
#guard_msgs in
set_option sym.debug true in
run_meta test ``Foo.ext_iff (mkApp3 (mkConst ``Eq [1]) fooNat (mkConst ``a) (mkConst ``b))

/-- info: step: a.x = b.x ∧ a.y = b.y -/
#guard_msgs in
set_option sym.debug true in
run_meta test ``foo_ext_iff (mkApp3 (mkConst ``Eq [1]) fooNat (mkConst ``a) (mkConst ``b))

def someEqNone : Expr := mkApp3 (mkConst ``Eq [1])
  (mkApp (mkConst ``Option [0]) (mkConst ``Nat))
  (mkApp2 (mkConst ``Option.some [0]) (mkConst ``Nat) (mkConst ``n))
  (mkApp (mkConst ``Option.none [0]) (mkConst ``Nat))

/-- info: step: False -/
#guard_msgs in
set_option sym.debug true in
run_meta test ``some_ne_none someEqNone

/-- info: step: True -/
#guard_msgs in
set_option sym.debug true in
run_meta test ``my_Q (mkApp2 (mkConst ``Q [1]) (mkConst ``Nat) (mkConst ``n))
