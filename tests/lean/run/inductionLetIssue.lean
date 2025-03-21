inductive P : Option Nat → Prop
  | none : P .none
  | somePos : x > 0 → P (some x)

theorem aux (x? : Option Nat) (h₁ : P x?) (h₂ : x?.isSome) : x?.get h₂ > 0 := by
  cases h₁ with
  | none => contradiction
  | somePos h => exact h

def f (x? : Option Nat) (hp : P x?) : { r? : Option Nat // P r? } :=
  if h₁ : x?.isSome then
    let x := x?.get h₁
    have : x > 0 := by
      cases h₂ : x with
      | zero => have := aux x? hp h₁; simp [x] at h₂; simp [h₂] at this; done
      | succ x' => simp +arith
    ⟨some x, .somePos this⟩
  else
    ⟨none, .none⟩

def f₁ (x : Nat) : Nat :=
  let y := x + 1
  by cases y with
     | zero => exact 2
     | succ y' => exact 1

example : f₁ x = 1 := rfl

noncomputable def f₂ (x : Nat) : Nat :=
  let y := x + 1
  by induction y with
     | zero => exact 2
     | succ y' => exact 1

example : f₂ x = 1 := rfl
