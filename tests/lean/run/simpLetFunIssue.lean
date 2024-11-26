example : (λ x => x)
           =
           (λ x : Nat =>
             let_fun foo := λ y => id (id y)
             foo (0 + x)) := by
  simp -zeta only [id]
  guard_target =ₛ
           (λ x => x)
           =
           (λ x : Nat =>
             let_fun foo := λ y => y
             foo (0 + x))
  simp
