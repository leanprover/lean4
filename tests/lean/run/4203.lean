class Fintype (α : Type u) where

class Preorder (α : Type u) extends LT α, LE α where
  lt := fun a b => a ≤ b ∧ ¬b ≤ a

structure Mappish (dIn dOut : Type u) [Fintype dIn] [Fintype dOut] where
  k : Nat

variable {dIn dOut dOut₂ : Type} [Fintype dIn] [Fintype dOut] [Fintype dOut₂]

def IsGood [DecidableEq dOut] [DecidableEq dOut₂] (Λ : Mappish dIn dOut) (Λ₂ : Mappish dIn dOut₂) : Prop :=
  ∃ (D : Mappish dOut (dOut₂)), D.k = Λ.k + Λ₂.k

/--
error: failed to synthesize
  Fintype v

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def MappishOrder [DecidableEq dIn] : Preorder
    (Σ dOut : Sigma (fun t ↦ Fintype t × DecidableEq t), let fin := dOut.snd.1; Mappish dIn dOut.fst) where
  le Λ₁ Λ₂ := by
    let u := Λ₁.fst.fst;
    let v := Λ₂.fst.fst;
    let ⟨w,x⟩ := Λ₁.fst.snd;
    let ⟨y,z⟩ := Λ₂.fst.snd;
    clear y;
    exact @IsGood dIn v u _ _ _ _ _ Λ₂.snd Λ₁.snd
