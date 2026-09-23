/-!
# Eta-for-structures agrees between the elaborator and the kernel

The `rfl` below used to be accepted by the elaborator but rejected by the kernel.
-/

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

/-- Both sides reduce to `mkNat e` applied to a proof of `F e`, which proof irrelevance identifies. -/
theorem succeeds (e : E) (x₁ : F e) (x₂ : F (E.mk e)) : mkNat e x₁ = mkNat (E.mk e) x₂ :=
  rfl
