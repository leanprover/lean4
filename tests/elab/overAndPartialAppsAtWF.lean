@[specialize]
def isEqvAux (a b : Array α) (hsz : a.size = b.size) (p : α → α → Bool) (i : Nat) : Bool :=
  if h : i < a.size then
     have : i < b.size := hsz ▸ h
     p a[i] b[i] && isEqvAux a b hsz p (i+1)
  else
    true
termination_by a.size - i
decreasing_by simp_wf; decreasing_trivial_pre_omega

theorem eq_of_isEqvAux [DecidableEq α] (a b : Array α) (hsz : a.size = b.size) (i : Nat) (hi : i ≤ a.size) (heqv : isEqvAux a b hsz (fun x y => x = y) i) : ∀ (j : Nat) (hl : i ≤ j) (hj : j < a.size), a[j] = b[j] := by
  intro j low high
  by_cases h : i < a.size
  · unfold isEqvAux at heqv
    simp [h] at heqv
    have hind := eq_of_isEqvAux a b hsz (i+1) (Nat.succ_le_of_lt h) heqv.2
    by_cases heq : i = j
    · subst heq; exact heqv.1
    · exact hind j (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne low heq)) high
  · have heq : i = a.size := Nat.le_antisymm hi (Nat.ge_of_not_lt h)
    subst heq
    exact absurd (Nat.lt_of_lt_of_le high low) (Nat.lt_irrefl j)
termination_by _ _ _ => a.size - i

@[simp] def f (x y : Nat) : Nat → Nat :=
  if h : x > 0 then
    fun z => f (x - 1) (y + 1) z + 1
  else
    (· + y)
termination_by x

#check f.eq_1
