inductive E : Type where
  | mk : E → E

inductive F : E → Prop
  | mk : F e → F (E.mk e)

theorem dec (x : F (E.mk e)) : F e ∧ True :=
  match x with
  | F.mk h => ⟨h, trivial⟩

def mkNat (e : E) (x : F e) : Nat :=
  match e with
  | E.mk e' =>
    match dec x with
    | ⟨h, _⟩ => mkNat e' h

theorem fail (e : E) (x₁ : F e) (x₂ : F (E.mk e)) : mkNat e x₁ = mkNat (E.mk e) x₂ :=
  /- The following rfl was succeeding in the elaborator but failing in the kernel because
     of a discrepancy in the implementation for Eta-for-structures. -/
  rfl -- should fail
