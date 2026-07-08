variable {α : Type}

theorem test1 {n : Nat} {f : Fin n → α} : False := by
  let c (i : Fin n) : Nat := i
  let d : Fin n → Nat × Nat := fun i => (c i, c i + 1)
  have : ∀ i, (d i).2 ≠ c i * 2 := by
    fail_if_success simp only -- should not unfold `d` or `i`
    guard_target =ₛ ∀ (i : Fin n), (d i).snd ≠ c i * 2
    simp +zetaDelta only -- `d` and `i` are now unfolded
    guard_target =ₛ ∀ (i : Fin n), i.val + 1 ≠ i.val * 2
    sorry
  sorry

opaque f : Nat → Nat
axiom f_ax (x : Nat): f (f x) = x

theorem test2 (a : Nat) : False := by
  let d : Nat → Nat × Nat := fun i => (f a, i)
  have : f (d 1).1 = a := by
    fail_if_success simp only [f_ax] -- f_ax should be applicable
    simp +zetaDelta only [f_ax] -- f_ax is applicable if zetaDelta := true
    done
  sorry
