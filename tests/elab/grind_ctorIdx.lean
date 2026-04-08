set_option warn.sorry false
set_option grind.debug true

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

-- Heteogeneous equality where the sides are not headed by the same type constructor

example (h : Bool = Nat) (x : Bool) (heq : x ≍ Nat.succ n) : x.ctorIdx = 0 := by
  fail_if_success grind
  sorry

-- Nat constructors are represented as `n + k` or as literals, so check that that works

example (n x1 : Nat) (h : Nat.hasNotBit 2 x1.ctorIdx) (heq_1 : x1 = n.succ) : False := by
  grind

example (n x1 : Nat) (h : Nat.hasNotBit 2 x1.ctorIdx) (heq_1 : x1 = n + 5) : False := by
  grind

example (x1 : Nat) (h : Nat.hasNotBit 2 x1.ctorIdx) (heq_1 : x1 = 5) : False := by
  grind

inductive S where
  | mk1 (n : Nat)
  | mk2 (n : Nat) (s : S)
  | mk3 (n : Bool)
  | mk4 (s1 s2 : S)

example (h : Nat.hasNotBit 5 x.ctorIdx) (heq_1 : x = S.mk1 n) : False := by grind

-- Some tests provided by claude

-- Test 1: Multiple ctorIdx comparisons with different constructors
example (t1 t2 : T) (h1 : t1 = .con1 10) (h2 : t2 = .con2) : t1.ctorIdx ≠ t2.ctorIdx := by
  grind

-- Test 2: ctorIdx with transitivity through multiple equalities
example (t1 t2 t3 : T) (h1 : t1 = t2) (h2 : t2 = t3) (h3 : t3 = .con1 7) : t1.ctorIdx = 0 := by
  grind

-- Test 3: ctorIdx inequality leading to false
example (t : T) (h1 : t = .con1 3) (h2 : t.ctorIdx = 1) : False := by
  grind

-- Test 4: ctorIdx with Option type (simple inductive with two constructors)
example (opt : Option Nat) (h : opt = .some 42) : opt.ctorIdx = 1 := by
  grind

example (opt : Option Nat) (h : opt = .none) : opt.ctorIdx = 0 := by
  grind

-- Test 5: ctorIdx distinguishing between constructors indirectly
example (opt1 opt2 : Option Nat) (h1 : opt1 = .some 5) (h2 : opt2 = .none)
    (heq : opt1.ctorIdx = opt2.ctorIdx) : False := by
  grind

-- Test 6: Dependent type with multiple index changes
example (n m : Nat) (v1 : Vec Nat n) (v2 : Vec Nat m)
    (hn : n = 0) (hm : m = 1)
    (hv1 : v1 ≍ (Vec.nil : Vec Nat 0)) (hv2 : v2 ≍ (Vec.cons 0 Vec.nil : Vec Nat 1))
    (hidx : v1.ctorIdx = v2.ctorIdx) : False := by
  grind

-- Test 7: ctorIdx with nested dependent types
inductive Fin' : Nat → Type where
| zero : {n : Nat} → Fin' (n + 1)
| succ : {n : Nat} → Fin' n → Fin' (n + 1)

example (n : Nat) (hn : n = 5) (f : Fin' n) (hf : f ≍ (Fin'.zero : Fin' 5)) : f.ctorIdx = 0 := by
  grind

-- Test 8: ctorIdx propagation through arithmetic
example (t : T) (h : t = .con2) (hbad : t.ctorIdx + 1 = 1) : False := by
  grind

-- Test 9: Complex heterogeneous equality with List
example (xs ys : List Nat)
    (hxs : xs = List.nil)
    (hys : ys = List.cons 0 List.nil)
    (hidx : xs.ctorIdx = ys.ctorIdx) : False := by
  grind

-- Test 10: ctorIdx with Sum type
example (s : Sum Nat Bool) (h : s = .inl 5) : s.ctorIdx = 0 := by
  grind

example (s : Sum Nat Bool) (h : s = .inr true) : s.ctorIdx = 1 := by
  grind
