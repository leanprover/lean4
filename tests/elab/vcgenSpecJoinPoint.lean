import Std.WP

set_option sym.debug true

/-!
A specification can bind a join point `__vcgen_jp` in a hypothesis, and `vcgen +jp` then proves the
join point's code once instead of once per jump. The language below is a deep embedding whose
`Spec.seq_ite` shares the code after an `if` this way.
-/

open Std.WP Lean.Order

set_option experimental.vcgen true

abbrev State := String → Nat

inductive Cmd where
  | skip
  | assign (x : String) (v : Nat)
  | seq (c₁ c₂ : Cmd)
  | ite (x : String) (c₁ c₂ : Cmd)
  /-- `check x` demands `x > 0`. -/
  | check (x : String)

def wpCmd : Cmd → (State → Prop) → State → Prop
  | .skip, Q, s => Q s
  | .assign x v, Q, s => Q (fun y => if y = x then v else s y)
  | .seq c₁ c₂, Q, s => wpCmd c₁ (wpCmd c₂ Q) s
  | .ite x c₁ c₂, Q, s => if s x ≠ 0 then wpCmd c₁ Q s else wpCmd c₂ Q s
  | .check x, Q, s => s x > 0 ∧ Q s

theorem wpCmd_mono {c : Cmd} {Q Q' : State → Prop} (h : ∀ s, Q s → Q' s) :
    ∀ s, wpCmd c Q s → wpCmd c Q' s := by
  induction c generalizing Q Q' with
  | skip => exact h
  | assign x v => intro s; exact h _
  | seq c₁ c₂ ih₁ ih₂ => intro s; exact ih₁ (ih₂ h) s
  | ite x c₁ c₂ ih₁ ih₂ =>
    intro s
    simp only [wpCmd]
    split
    · exact ih₁ h s
    · exact ih₂ h s
  | check x => intro s ⟨hx, hq⟩; exact ⟨hx, h s hq⟩

instance : WP Cmd Unit (State → Prop) EStack⟨⟩ where
  trans c := PredTrans.mk (fun Q _ s => wpCmd c (Q ()) s) fun hQ _ s h =>
    wpCmd_mono (fun s' h' => hQ () s' h') s h

section Specs

variable {Q : Unit → State → Prop} {eposts : EStack⟨⟩}

theorem triple_of_wp {c : Cmd} {pre : State → Prop}
    (h : ∀ s, wp c Q eposts s = pre s) : Triple c pre Q eposts :=
  Triple.iff.mpr (by rw [funext h]; exact PartialOrder.rel_refl)

@[spec] theorem Spec.skip : Triple Cmd.skip (Q ()) Q eposts := triple_of_wp fun _ => rfl

@[spec] theorem Spec.assign (x : String) (v : Nat) :
    Triple (Cmd.assign x v) (fun s => Q () (fun y => if y = x then v else s y)) Q eposts :=
  triple_of_wp fun _ => rfl

@[spec] theorem Spec.seq (c₁ c₂ : Cmd) :
    Triple (Cmd.seq c₁ c₂) (wp c₁ (fun _ => wp c₂ Q eposts) eposts) Q eposts :=
  triple_of_wp fun _ => rfl

@[spec] theorem Spec.ite (x : String) (c₁ c₂ : Cmd) :
    Triple (Cmd.ite x c₁ c₂)
      (fun s => if s x ≠ 0 then wp c₁ Q eposts s else wp c₂ Q eposts s) Q eposts :=
  triple_of_wp fun _ => rfl

@[spec] theorem Spec.check (x : String) :
    Triple (Cmd.check x) (fun s => s x > 0 ∧ Q () s) Q eposts :=
  triple_of_wp fun _ => rfl

/-- The code `c₃` after an `if` runs at the end of both branches, through the join point
`__vcgen_jp`. -/
@[spec default+10] theorem Spec.seq_ite (x : String) (c₁ c₂ c₃ : Cmd) :
    Triple (Cmd.seq (Cmd.ite x c₁ c₂) c₃)
      (fun s => have __vcgen_jp := fun (_ : Unit) => c₃
        wp (Cmd.ite x (Cmd.seq c₁ (__vcgen_jp ())) (Cmd.seq c₂ (__vcgen_jp ()))) Q eposts s) Q eposts :=
  triple_of_wp fun _ => rfl

end Specs

/-- `check "y"` after the `if` is one verification condition under `+jp`, and one per branch
without it. -/
def prog : Cmd := .seq (.ite "b" (.assign "x" 1) (.assign "x" 2)) (.check "y")

/--
trace: case vc1
s✝ : String → Nat
x✝¹ : PUnit
x✝ : String → Nat
h✝ :
  (¬s✝ "b" = 0 ∧ x✝ = fun y => if y = "x" then 1 else s✝ y) ∨ ¬¬s✝ "b" = 0 ∧ x✝ = fun y => if y = "x" then 2 else s✝ y
⊢ 0 < x✝ "y"
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : Triple prog (fun _ => True) (fun _ _ => True) ⊥ := by
  vcgen +jp [prog]
  trace_state
  all_goals sorry

/--
trace: case vc1
s✝ : String → Nat
h✝ : ¬s✝ "b" = 0
⊢ 0 < s✝ "y"

case vc2
s✝ : String → Nat
h✝ : ¬¬s✝ "b" = 0
⊢ 0 < s✝ "y"
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : Triple prog (fun _ => True) (fun _ _ => True) ⊥ := by
  vcgen [prog]
  trace_state
  all_goals sorry
