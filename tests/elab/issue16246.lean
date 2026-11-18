/-!
Regression test for #16246: the statement of an equation lemma can contain cast proofs that mention
constants created while computing the statement, such as `f.match_1.eq_1`. These must be available
when the equation lemma is added.
-/

def f : Nat :=
  Nat.divExact (2 * (match 0 with | 0 => 1 | _ => 3)) _ (Nat.dvd_mul_left _ 2)

theorem t : f = 2 := by simp [f]

/-- info: f.eq_1 : f = (2 * 1).divExact 1 ⋯ -/
#guard_msgs in
#check f.eq_1

/-! The cast proof in the statement also mentions `Nat.divExact.congr_simp`. -/

def nested : Nat :=
  Nat.divExact
    (2 * Nat.divExact (2 * (match 0 with | 0 => 1 | _ => 3)) _ (Nat.dvd_mul_left _ 2)) _
    (Nat.dvd_mul_left _ 2)

theorem nested_eq : nested = 2 := by simp [nested]

/-! A recursive function, reusing the matcher of `f`. -/

def recf : Nat → Nat
  | 0 => 0
  | n + 1 => recf n + Nat.divExact (2 * (match 0 with | 0 => 1 | _ => 3)) _ (Nat.dvd_mul_left _ 2)

theorem recf_succ (n : Nat) : recf (n + 1) = recf n + 2 := by simp [recf]
