import Std

variable {ps : Type u}

class TransShape (ps : Type u) where
  Assertion : Type u
  ExceptConds : Type u

open TransShape (Assertion ExceptConds)

abbrev PostCond (α : Type u) (ps : Type u) [TransShape ps] :=
  (α → Assertion ps) ×' ExceptConds ps

class TransShape.Entails (ps : Type u) extends TransShape ps where
  assertionEntails : Assertion → Assertion → Prop
  exceptCondsEntails : ExceptConds → ExceptConds → Prop

abbrev TransShape.Entails.postCondEntails [TransShape.Entails ps]
  (p q : PostCond α ps) : Prop :=
  (∀ a, assertionEntails (p.1 a) (q.1 a)) ∧ exceptCondsEntails p.2 q.2

infixr:25 " ⊢ₛ " => TransShape.Entails.assertionEntails
infixr:25 " ⊢ₑ " => TransShape.Entails.exceptCondsEntails
infixr:25 " ⊢ₚ " => TransShape.Entails.postCondEntails

class TransShape.EntailsPre (ps : Type u) extends TransShape.Entails ps where
  assertionPreorder : @Std.IsPreorder Assertion ⟨assertionEntails⟩
  exceptCondsPreorder : @Std.IsPreorder ExceptConds ⟨exceptCondsEntails⟩

theorem TransShape.EntailsPre.postCondPreorder [TransShape.EntailsPre ps]
  : @Std.IsPreorder (PostCond α ps) ⟨TransShape.Entails.postCondEntails⟩ :=
  let : LE (PostCond α ps) := ⟨TransShape.Entails.postCondEntails⟩
  let ap := assertionPreorder (ps := ps)
  let ep := exceptCondsPreorder (ps := ps)
  { le_refl x := by
      constructor
      · intro a; apply ap.le_refl
      · apply ep.le_refl
  , le_trans := by
      intro x y z hxy hyz
      constructor
      · intro a; apply ap.le_trans _ _ _ (hxy.1 a) (hyz.1 a)
      · apply ep.le_trans _ _ _ (hxy.2) (hyz.2)
  }

/-- The stronger the postcondition, the stronger the transformed precondition. -/
def PredTrans.Monotonic [TransShape.Entails ps] (t : PostCond α ps → Assertion ps) : Prop :=
  ∀ Q₁ Q₂, (Q₁ ⊢ₚ Q₂) → (t Q₁) ⊢ₛ (t Q₂)

/--
  The type of predicate transformers for a given `ps : TransShape` and return type `α : Type`.
  A predicate transformer `x : PredTrans ps α` is a function that takes a postcondition
  `Q : PostCond α ps` and returns a precondition `x.apply Q : Assertion ps`.
 -/
@[ext]
structure PredTrans (ps : Type u) [TransShape.Entails ps] (α : Type u) : Type u where
  /-- Apply the predicate transformer to a postcondition. -/
  apply : PostCond α ps → Assertion ps
  mono : PredTrans.Monotonic apply
  /-- The predicate transformer is conjunctive: `t (Q₁ ∧ₚ Q₂) ⊣⊢ₛ t Q₁ ∧ t Q₂`.
  So the stronger the postcondition, the stronger the resulting precondition. -/
  -- conjunctive : PredTrans.Conjunctive apply

structure Prop' : Type u
structure PMF' (α : Type u) : Type u
structure Arg' (σ : Type u) (ps : Type u) : Type u
structure Except' (ε : Type u) (ps : Type u) : Type u

instance : TransShape Prop' where
  Assertion := ULift Prop
  ExceptConds := PUnit

instance [inst : TransShape ps'] : TransShape (Arg' σ ps') where
  Assertion := σ → Assertion ps'
  ExceptConds := inst.ExceptConds

instance [inst : TransShape ps'] : TransShape (Except' ε ps') where
  Assertion := inst.Assertion
  ExceptConds := (ε → inst.Assertion) ×' inst.ExceptConds

example : Assertion (Arg' σ (Except' ε Prop')) :=
  fun s => ULift.up True
example : PostCond α (Arg' σ Prop') :=
  ⟨fun r s => ULift.up True, ⟨⟩⟩
example : PostCond α (Arg' σ (Except' ε Prop')) :=
  ⟨fun r s => ULift.up True, fun e => ULift.up False, ⟨⟩⟩
example : PostCond α (Except' ε (Arg' σ (Except' ε Prop'))) :=
  ⟨fun r s => ULift.up True, fun e s => ULift.up False, fun e => ULift.up False, ⟨⟩⟩

class WP (m : Type u → Type v) (ps : outParam (Type u)) extends TransShape ps where
  wp : ∀ {α}, m α → PredTrans ps α

instance : WP Id Prop' := sorry
instance [WP m ps] : WP (StateT σ m) (Arg' σ ps) := sorry
instance [WP m ps] : WP (ExceptT ε m) (Except' ε ps) := sorry
instance : WP (EStateM ε σ) (Except' ε (Arg' σ Prop')) := sorry

def Triple [WP m ps] (x : m α) (P Q : α → Assertion ps) := True

theorem spec {α : Type} {ps} [WP m ps] (prog : m α) (P : α → Assertion ps) :
  Triple prog P P := sorry

#guard_msgs (error) in
#check (spec _ (fun p s => p.1 = p.2 ∧ s = 4)
        : @Triple (MProd (Option Nat) Nat) (Arg' Nat Prop') _ _ _ _ _)

#check ∀ ε σ α s (prog : EStateM ε σ α) (P : σ → Prop),
    Triple prog (fun s' => s' = s) P → P s
