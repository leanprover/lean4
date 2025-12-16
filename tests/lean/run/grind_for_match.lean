import Lean

set_option warn.sorry false

set_option debug.Meta.Match.MatchEqs.unrestrictedGrind false

elab "grind_for_match" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  Lean.Meta.Grind.withProtectedMCtx (abstractProof := false) mvarId fun mvarId =>
    Lean.Meta.Match.grind mvarId

inductive T where
| con1 : Nat → T
| con2 : T

opaque double (n : Nat) : T := .con2

example (heq_1 : double n = .con1 5) : (double n).ctorIdx = 0 := by
  grind_for_match

example  (h : (double n).ctorIdx > 5) (heq_1 : double n = .con1 5) : False := by
  grind_for_match

example  (h : Nat.hasNotBit 1 0) : False := by
  grind_for_match

example  (h : Nat.hasNotBit 1 (double n).ctorIdx) (heq_1 : double n = .con1 5) : False := by
  grind_for_match

inductive IT : Nat → Type where
| con1 n : IT n
| con2 : IT 0

-- But this works, thanks to the `.ctorIdx.hinj` theorem
example (hm : m = 4) (heq_1 : (x : IT m) ≍ (IT.con1 4)) : x.ctorIdx = 0 := by
  grind_for_match

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
  grind_for_match


inductive EvenVec (α : Type) : (n : Nat) → (n % 2 = 0) → Type where
| nil  : EvenVec α 0 (by rfl)
| cons n p : α → EvenVec α n p → EvenVec α (n + 2) (by grind)

example (hα : α = α') (_ : double n = double m)
    (_ : Nat.double n = k + 2)
    (xs : EvenVec α (.double n) p1) (x' : α') (xs' : EvenVec α' k p2)
    (heq : xs ≍ EvenVec.cons _ p3 x' xs') :
    xs.ctorIdx = 1 := by
  grind_for_match

-- Heteogeneous equality where the sides are not headed by the same type constructor

example (h : Bool = Nat) (x : Bool) (heq : x ≍ Nat.succ n) : x.ctorIdx = 0 := by
  fail_if_success grind_for_match
  sorry

-- Nat constructors are represented as `n + k` or as literals, so check that that works

example (n x1 : Nat) (heq_1 : x1 = n.succ) : x1.ctorIdx = 1 := by
  grind_for_match

example (n x1 : Nat) (h : Nat.hasNotBit 2 x1.ctorIdx) (heq_1 : x1 = n.succ) : False := by
  grind_for_match

example (n x1 : Nat) (h : Nat.hasNotBit 2 x1.ctorIdx) (heq_1 : x1 = n + 5) : False := by
  grind_for_match

example (x1 : Nat) (h : Nat.hasNotBit 2 x1.ctorIdx) (heq_1 : x1 = 5) : False := by
  grind_for_match

inductive S where
  | mk1 (n : Nat)
  | mk2 (n : Nat) (s : S)
  | mk3 (n : Bool)
  | mk4 (s1 s2 : S)

example (h : Nat.hasNotBit 5 x.ctorIdx) (heq_1 : x = S.mk1 n) : False := by grind_for_match

-- Int constructor injectivity

example (heq : Int.ofNat x = Int.ofNat n) : x = n := by
  grind_for_match

example (heq : Int.negSucc x = Int.negSucc n) : x = n := by
  grind_for_match
