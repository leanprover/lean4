import Lean
open Lean Meta Elab Tactic

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw)
  let methods : Sym.Simp.Methods := { post := Sym.Simp.evalGround.andThen rewrite }
  liftMetaTactic1 <| Sym.simpWith (Sym.simp · methods)

example : (1-1) + x*1 + (2-1)*0 = x := by
  sym_simp [Nat.add_zero, Nat.zero_add, Nat.mul_one]

opaque f : Nat → Nat
axiom fax : x > 10 → f x = 0

example : f 12 = 0 := by
  sym_simp [fax]
