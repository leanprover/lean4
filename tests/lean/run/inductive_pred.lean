namespace Ex
inductive LE : Nat → Nat → Prop
  | refl : LE n n
  | succ : LE n m → LE n m.succ

theorem LE.trans : LE m n → LE n o → LE m o := by
  intro h1 h2
  induction h2 with
  | refl => assumption
  | succ h2 ih => exact succ (ih h1)

theorem LE.trans' : LE m n → LE n o → LE m o
  | h1, refl    => h1
  | h1, succ h2 => succ (trans' h1 h2) -- the structural recursion in being performed on the implicit `Nat` parameter

inductive Even : Nat → Prop
  | zero : Even 0
  | ss   : Even n → Even n.succ.succ

theorem Even.add : Even n → Even m → Even (n+m) := by
  intro h1 h2
  induction h2 with
  | zero => exact h1
  | ss h2 ih => exact ss ih

theorem Even.add' : Even n → Even m → Even (n+m)
  | h1, zero  => h1
  | h1, ss h2 => ss (add' h1 h2)  -- the structural recursion in being performed on the implicit `Nat` parameter

theorem mul_left_comm (n m o : Nat) : n * (m * o) = m * (n * o) := by
  rw [← Nat.mul_assoc, Nat.mul_comm n m, Nat.mul_assoc]

inductive Power2 : Nat → Prop
  | base : Power2 1
  | ind  : Power2 n → Power2 (2*n) -- Note that index here is not a constructor

theorem Power2.mul : Power2 n → Power2 m → Power2 (n*m) := by
  intro h1 h2
  induction h2 with
  | base      => simp_all
  | ind h2 ih => exact mul_left_comm .. ▸ ind ih

/- The following example fails because the structural recursion cannot be performed on the `Nat`s and
   the `brecOn` construction doesn't work for inductive predicates -/
-- theorem Power2.mul' : Power2 n → Power2 m → Power2 (n*m)
--  | h1, base => by simp_all
--  | h1, ind h2 => mul_left_comm .. ▸ ind (mul' h1 h2)
end Ex
