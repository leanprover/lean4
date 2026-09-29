import Lean

/-! # Regression test for `Sym.dsimp` telescopes with dependent binder types

`mkForallFVarsS`/`mkLambdaFVarsS` must abstract the free variables of the *earlier* binders in
each binder type. They used to abstract the wrong range, so a binder type mentioning an earlier
binder kept a dangling free variable (e.g. `∀ k, _fvar < 32 → ...`). Minimized from a `bv_decide`
failure reported in #15195. -/

open Lean Meta Elab Tactic Sym Sym.DSimp

elab "sym_dsimp_hyp " h:ident : tactic => withMainContext do
  let fvarId ← getFVarId h
  let methods : Methods := { pre := zetaDeltaAll }
  let r ← SymM.run do
    let e ← Sym.shareCommon (← instantiateMVars (← fvarId.getType))
    Sym.dsimp e (methods := methods)
  logInfo m!"result: {r}"
  Meta.check r

/-- info: result: ∀ (k : Nat), k < 32 → y.toNat = y.toNat -/
#guard_msgs in
example (y : BitVec 256) : True := by
  let x : BitVec 256 := y
  have h : ∀ k : Nat, k < 32 → x.toNat = x.toNat := fun _ _ => rfl
  sym_dsimp_hyp h
  trivial

/-! The binder type itself is rewritten (`k < x.toNat` ↦ `k < y.toNat`) and mentions `k`. -/

/-- info: result: ∀ (k : Nat), k < y.toNat → k = k -/
#guard_msgs in
example (y : BitVec 256) : True := by
  let x : BitVec 256 := y
  have h : ∀ k : Nat, k < x.toNat → k = k := fun _ _ => rfl
  sym_dsimp_hyp h
  trivial

/-! Deeper telescope: each binder type depends on all previous binders. -/

/-- info: result: ∀ (a : Nat) (b : Fin a) (c : Fin ↑b), ↑c < y.toNat -/
#guard_msgs in
set_option warn.sorry false in
example (y : BitVec 256) : True := by
  let x : BitVec 256 := y
  have h : ∀ (a : Nat) (b : Fin a) (c : Fin b.val), c.val < x.toNat := sorry
  sym_dsimp_hyp h
  trivial

/-! Lambda telescopes use `mkLambdaFVarsS`. -/

/-- info: result: (fun (k : Nat) (x : k < 32) => y.toNat) = fun (k : Nat) (x : k < 32) => y.toNat -/
#guard_msgs in
set_option pp.funBinderTypes true in
example (y : BitVec 256) : True := by
  let x : BitVec 256 := y
  have h : (fun (k : Nat) (_ : k < 32) => x.toNat) = (fun (k : Nat) (_ : k < 32) => x.toNat) := rfl
  sym_dsimp_hyp h
  trivial

/-! The original report: `bv_decide` preprocesses the context with `Sym.dsimp`. -/

example (y : BitVec 256) : True := by
  let x : BitVec 256 := y
  have h : ∀ k : Nat, k < 32 → x.toNat = x.toNat := fun _ _ => rfl
  have t : (0#64) ≤ (1#64) := by bv_decide
  trivial
