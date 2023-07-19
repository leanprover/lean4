opaque f : Nat → Nat
opaque q : Nat → Prop
opaque r : Nat → Prop

@[simp] axiom ax1 (p : Prop) : (p ∧ True) ↔ p
@[simp] axiom ax2 (x : Nat) : q (f x)
@[simp] axiom ax3 (x : Nat) : ¬ r (f x)
@[simp] axiom ax4 (p : Prop) : (p ∨ False) ↔ p

theorem ex1 (x : Nat) (h : q x) : q x ∧ q (f x) := by
  simp [h]

theorem ex2 (x : Nat) : q (f x) ∨ r (f x) := by
  simp

@[simp] axiom ax5 (x : Nat) : 0 + x = x

theorem ex3 (h : 0 + x = y) : f x = f y := by
  simp at h
  simp [h]

theorem ex4 (x y z : Nat) (h : (x, z).1 = y) : f x = f y := by
  simp at h
  simp [h]

theorem ex5
    (f  : Nat → Nat → Nat)
    (g  : Nat → Nat)
    (h₁ : ∀ x, f x x = x)
    (h₂ : ∀ x, g (g x) = x)
    : f (g (g x)) (f x x) = x :=
  by simp [h₁, h₂]

@[simp] axiom ax6 (x : Nat) : x + 0 = x

theorem ex6
  (f : Nat → Nat)
  (x y : Nat)
  : (fun (h : y = 0) => y + x) = (fun _ => x + 0) := by
 simp (config := { contextual := true })

theorem ex7 (x : Nat) : (let y := x + 0; y + y) = x + x := by
  simp

@[simp] theorem impTrue (p : Sort u) : (p → True) = True :=
  propext <| Iff.intro (fun _ => trivial) (fun _ _ => trivial)

theorem ex8 (y x : Nat) : y = 0 → x + y = 0 → x = 0 := by
  simp (config := { contextual := true })

theorem ex9 (y x : Nat) : y = 0 → x + y = 0 → x = 0 := by
  fail_if_success simp
  intro h₁ h₂
  simp [h₁] at h₂
  simp [h₂]

theorem ex10 (y x : Nat) : y = 0 → x + 0 = 0 → x = 0 := by
  simp
  intro h₁ h₂
  simp [h₂]

theorem ex11 : ∀ x : Nat, 0 + x + 0 = x := by
  simp
