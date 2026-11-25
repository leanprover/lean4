import Lean
/-!
Regression test for #14949: unification must not assign an instance to an instance-implicit
metavariable when the types of the two agree only after unfolding a type synonym.
-/

/-! The projection `(?inst).toA =?= i.toA` must not assign `?inst := i` when `?inst : B (Syn Nat)`
and `i : B Nat`, also when `Syn` is `implicit_reducible`. The synonym `Syn Nat` has its own
instance, and that instance has a different `toA` field. -/
section Projection
open Lean Meta

class A (α : Type) where a : Nat
class B (α : Type) extends A α where b : Nat
@[implicit_reducible] def Syn (α : Type) : Type := α
instance instBSyn : B (Syn Nat) := { a := 1, b := 1 }
@[instance_reducible] def instBNat : B Nat := { a := 0, b := 0 }

/-- info: false -/
#guard_msgs in
run_meta do
  let inst ← mkFreshExprMVar (mkApp (mkConst ``B) (mkApp (mkConst ``Syn) (mkConst ``Nat))) .synthetic
  let lhs := mkApp2 (mkConst ``B.toA) (mkApp (mkConst ``Syn) (mkConst ``Nat)) inst
  let rhs := mkApp2 (mkConst ``B.toA) (mkConst ``Nat) (mkConst ``instBNat)
  logInfo m!"{← isDefEq lhs rhs}"

end Projection

/-! The reproducer from the issue: the elaborator must not take `inst✝²`, the instance of the
synonym's source type, for the `Nrm (Tan E B b)` argument of `inner_bundle`. -/
section Reproducer

class Topo (α : Type) where nhd : α → α → Prop
class Nrm (α : Type) extends Topo α where norm : α → Nat
structure Total {B : Type} (E : B → Type) where
  base : B
  fib  : E base

class Fib {B : Type} (E : B → Type) [∀ b, Topo (E b)] where chart : B → B

instance totalTopo {B : Type} [Topo B] {E : B → Type} [∀ b, Topo (E b)] [Fib E] :
    Topo (Total E) := ⟨fun _ _ => True⟩

def Diff {M N : Type} [Topo M] [Topo N] (_f : M → N) : Prop := True

theorem inner_bundle {B : Type} [Topo B] {E : B → Type}
    [nE : ∀ b, Nrm (E b)] [Fib E] {f g : ∀ b, E b}
    (_hf : Diff fun b => (⟨b, f b⟩ : Total E))
    (_hg : Diff fun b => (⟨b, g b⟩ : Total E)) :
    ∀ b, (nE b).norm (f b) + (nE b).norm (g b) = (nE b).norm (g b) + (nE b).norm (f b) :=
  fun _ => Nat.add_comm ..

def Tan (E : Type) (B : Type) (_b : B) : Type := E

instance tanTopo (E : Type) [nE : Nrm E] (B : Type) (b : B) : Topo (Tan E B b) := nE.toTopo
instance tanFib (E : Type) [Nrm E] (B : Type) : Fib (Tan E B) := ⟨id⟩

class RB {B : Type} (E : B → Type) [∀ b, Topo (E b)] where g : ∀ b, E b → Nat

instance rbNrm {B : Type} {E : B → Type} [tE : ∀ b, Topo (E b)] [rb : RB E] (b : B) : Nrm (E b) where
  toTopo := tE b
  norm := rb.g b

variable (E : Type) [Nrm E] (B : Type) [Topo B] [RB (Tan E B)] (f g : ∀ b, Tan E B b)
variable (hf : Diff fun b => (⟨b, f b⟩ : Total (Tan E B)))
  (hg : Diff fun b => (⟨b, g b⟩ : Total (Tan E B)))

/-- info: inner_bundle hf hg : ∀ (b : B), Nrm.norm (f b) + Nrm.norm (g b) = Nrm.norm (g b) + Nrm.norm (f b) -/
#guard_msgs in
#check inner_bundle hf hg

example : ∀ b, (rbNrm b).norm (f b) + (rbNrm b).norm (g b) = (rbNrm b).norm (g b) + (rbNrm b).norm (f b) :=
  inner_bundle hf hg

end Reproducer
