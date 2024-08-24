import Lean
open Lean Elab Meta Tactic
opaque foo (p : Prop) [Decidable p] : Prop
class PropClass (n : Nat) : Prop where
opaque P1 (n : Nat) [PropClass n] : Prop
class TypeClass (n : Nat) : Type where
opaque P2 (n : Nat) [TypeClass n] : Prop

/--
info: thm for foo: ∀ (p p_1 : Prop), p = p_1 → ∀ {inst : Decidable p} {inst_1 : Decidable p_1}, foo p = foo p_1
kinds: #[Lean.Meta.CongrArgKind.eq, Lean.Meta.CongrArgKind.subsingletonInst]
---
info: thm for P1: ∀ (n n_1 : Nat) (e_n : n = n_1) [inst : PropClass n], P1 n = P1 n_1
kinds: #[Lean.Meta.CongrArgKind.eq, Lean.Meta.CongrArgKind.cast]
---
info: thm for P2: ∀ (n : Nat) [inst : TypeClass n], P2 n = P2 n
kinds: #[Lean.Meta.CongrArgKind.fixed, Lean.Meta.CongrArgKind.fixed]
-/
#guard_msgs in
run_meta
  #[``foo, ``P1, ``P2].forM fun n => do
    let e ← mkConstWithLevelParams n
    let some thm ← mkCongrSimp? e (subsingletonInstImplicitRhs := false) | throwError "no thm"
    let kinds ← getCongrSimpKinds e (← getFunInfo e)
    logInfo m!"thm for {e}: {thm.type}\nkinds: {repr kinds}"

example [Decidable p] [Decidable (id p)] (h : foo p) : foo (id p) := by
  conv => arg 1; rw [id]
  exact h

/--
error: tactic 'fail' failed
p : Prop
inst✝ : Decidable p
⊢ Decidable (id p)
---
error: unsolved goals
p : Prop
inst✝ : Decidable p
⊢ foo (id p)
-/
#guard_msgs in
example [Decidable p] : foo p := by
  conv =>
    arg 1
    · rw [← id.eq_def p]
    · tactic => fail

example [PropClass n] [PropClass (id n)] (h : P1 n) : P1 (id n) := by
  conv => arg 1; rw [id]
  exact h

example [PropClass n] (h : P1 n) : P1 n := by
  conv => arg 1; rw [← id.eq_def n]
  conv => arg 1; rw [id.eq_def n]
  exact h

/-- error: cannot select argument -/
#guard_msgs in
example [TypeClass n] [TypeClass (id n)] (h : P2 n) : P2 (id n) := by
  conv => arg 1
