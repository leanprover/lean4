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

example (a : Nat) (h : a = b) : (let_fun x := 1*a; 0 + x) = 0 + b := by
   simp -zeta only [Nat.zero_add]
   guard_target =ₛ
       (let_fun x := 1 * a; x) = b
   simp -zeta only [Nat.one_mul]
   guard_target =ₛ
       (let_fun x := a; x) = b
   simp [h]

example (a : Nat) (h : a = b) : (let_fun x := 1*a; 0 + x) = 0 + b := by
   simp -zeta only [Nat.zero_add, Nat.one_mul]
   guard_target =ₛ
       (let_fun x := a; x) = b
   simp [h]

example (a : Nat) (h : a = b) : (let_fun _y := 0; let_fun x := 1*a; 0 + x) = 0 + b := by
   simp -zeta only [Nat.zero_add, Nat.one_mul]
   guard_target =ₛ
       (let_fun x := a; x) = b
   simp [h]

example (a : Nat) (h : a = b) : (let_fun y := 0; let_fun x := y*0 + 1*a; 0 + x) = 0 + b := by
   simp -zeta only [Nat.zero_add, Nat.one_mul, Nat.mul_zero]
   guard_target =ₛ
       (let_fun x := a; x) = b
   simp [h]

set_option pp.all true
example (a : Nat) (h : a = b) : (let_fun y := 0; let_fun x := y*0 + 1*a; 0 + x) = 0 + b := by
   simp -zeta only [Nat.zero_add, Nat.one_mul]
   guard_target =ₛ
       (let_fun y := 0; let_fun x := y*0 + a; x) = b
   done
   simp -zeta only [Nat.zero_add, Nat.one_mul]
   simp -zeta only [Nat.zero_add, Nat.one_mul]
   simp -zeta only [Nat.zero_add, Nat.one_mul]
   simp -zeta only [Nat.zero_add, Nat.one_mul]
   simp -zeta only [Nat.zero_add, Nat.one_mul]
   done
   sorry -- simp [h]
