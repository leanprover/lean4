import Lean
open Lean Meta Elab Tactic

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeSimpSelf
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpControl
    post := Sym.Simp.evalGround.andThen rewrite
  }
  liftMetaTactic1 <| Sym.simpWith (Sym.simp · methods)

example : (1-1) + x*1 + (2-1)*0 = x := by
  sym_simp [Nat.add_zero, Nat.zero_add, Nat.mul_one]

opaque f : Nat → Nat
axiom fax : x > 10 → f x = 0

example : f 12 = 0 := by
 sym_simp [fax]

example : (if true then a else b) = a := by
  sym_simp []

example (f g : Nat → Nat) : (if a + 0 = a then f else g) a = f a := by
  sym_simp [Nat.add_zero]

example (f g : Nat → Nat → Nat) : (if a + 0 ≠ a then f else g) a (b + 0) = g a b := by
  sym_simp [Nat.add_zero]

/--
trace: a b : Nat
f g : Nat → Nat → Nat
h : a = b
⊢ (if a ≠ b then id f else id (id g)) a (b + 0) = g a b
-/
#guard_msgs in
example (f g : Nat → Nat → Nat) (h : a = b) : (if a + 0 ≠ b then id f else id (id g)) a (b + 0) = g a b := by
  sym_simp [Nat.add_zero, id_eq]
  trace_state -- `if-then-else` branches should not have been simplified
  subst h
  sym_simp [Nat.add_zero, id_eq]
