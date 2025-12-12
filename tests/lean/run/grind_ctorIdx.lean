set_option warn.sorry false

inductive T where
| con1 : Nat → T
| con2 : T

opaque double (n : Nat) : T := .con2


example (heq_1 : double n = .con1 5) : (double n).ctorIdx = 0 := by
  grind

example  (h : (double n).ctorIdx > 5) (heq_1 : double n = .con1 5) : False := by
  grind

example  (h : Nat.hasNotBit 1 0) : False := by
  grind

example  (h : Nat.hasNotBit 1 (double n).ctorIdx) (heq_1 : double n = .con1 5) : False := by
  grind

inductive IT : Nat → Type where
| con1 n : IT n
| con2 : IT 0

-- This should not work: we cannot conclude anything about `x.ctorIdx` without knowing `m`.
example (heq_1 : (x : IT m) ≍ (IT.con1 4)) : x.ctorIdx = 0 := by
  fail_if_success grind
  sorry

-- But this works, thanks to the `.ctorIdx.hinj` theorem
example (hm : m = 4) (heq_1 : (x : IT m) ≍ (IT.con1 4)) : x.ctorIdx = 0 := by
  grind

-- More dependent examples

opaque Nat.double (n : Nat) : Nat := n + n

inductive Vec (α : Type) : Nat → Type where
| nil  : Vec α 0
| cons : {n : Nat} → α → Vec α n → Vec α (Nat.succ n)

example
    (n k : Nat)
    (hα : α = α')
    (_ : Nat.double n = k + 1)
    (xs : Vec α (.double n)) (x : α') (xs' : Vec α' k)
    (heq : xs ≍ Vec.cons x xs') :
    xs.ctorIdx = 1 := by
  grind


inductive EvenVec (α : Type) : (n : Nat) → (n % 2 = 0) → Type where
| nil  : EvenVec α 0 (by rfl)
| cons n p : α → EvenVec α n p → EvenVec α (n + 2) (by grind)

example (hα : α = α') (_ : double n = double m)
    (_ : Nat.double n = k + 2)
    (xs : EvenVec α (.double n) p1) (x' : α') (xs' : EvenVec α' k p2)
    (heq : xs ≍ EvenVec.cons _ p3 x' xs') :
    xs.ctorIdx = 1 := by
  grind
