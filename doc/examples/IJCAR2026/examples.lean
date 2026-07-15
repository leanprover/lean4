/- Examples from the paper "grind: An SMT-Inspired Tactic for Lean 4" -/
open Lean Grind

/- Congruence closure. -/

example (f : Nat → Nat) (h : a = b) : f (f b) = f (f a) := by grind

/-
E-matching.

Any `f` that is the left inverse of `g` would work on this example.
-/
def f (x : Nat) := x - 1
def g (x : Nat) := x + 1

@[grind =] theorem fg : f (g x) = x := by simp [f, g]
example : f a = b → a = g c → b = c := by grind

/-
Any `R` that is transitive and symmetric would work on this example.
-/
def R : Nat → Nat → Prop := (· % 7 = · % 7)
@[grind →] theorem Rtrans : R x y → R y z → R x z := by grind [R]
@[grind →] theorem Rsymm  : R x y → R y x := by grind [R]
example : R a b → R c b → R d c → R a d := by grind

/- Big step operational semantics example. -/

abbrev Variable := String
def State := Variable → Nat
inductive Stmt : Type where
  | skip : Stmt
  | assign : Variable → (State → Nat) → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo : (State → Prop) → Stmt → Stmt
infix:60 ";; " => Stmt.seq
export Stmt (skip assign seq ifThenElse whileDo)
set_option quotPrecheck false in
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)
inductive BigStep : Stmt → State → State → Prop where
  | skip (s : State) : BigStep skip s s
  | assign (x : Variable) (a : State → Nat) (s : State) : BigStep (assign x a) s (s[x ↦ a s])
  | seq {S T : Stmt} {s t u : State} (hS : BigStep S s t) (hT : BigStep T t u) :
    BigStep (S;; T) s u
  | if_true {B : State → Prop} {s t : State} (hcond : B s) (S T : Stmt) (hbody : BigStep S s t) :
    BigStep (ifThenElse B S T) s t
  | if_false {B : State → Prop} {s t : State} (hcond : ¬ B s) (S T : Stmt) (hbody : BigStep T s t) :
    BigStep (ifThenElse B S T) s t
  | while_true {B S s t u} (hcond : B s) (hbody : BigStep S s t) (hrest : BigStep (whileDo B S) t u) :
    BigStep (whileDo B S) s u
  | while_false {B S s} (hcond : ¬ B s) : BigStep (whileDo B S) s s
notation:55 "(" S:55 "," s:55 ")" " ==> " t:55 => BigStep S s t

example {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  grind [cases BigStep]

theorem cases_if_of_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  grind [cases BigStep]

theorem cases_if_of_false {B S T s t} (hcond : ¬ B s) : (ifThenElse B S T, s) ==> t → (T, s) ==> t := by
  grind [cases BigStep]

example {B S T s t} : (ifThenElse B S T, s) ==> t ↔ (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  grind [BigStep] -- shortcut for `cases BigStep` and `intro BigStep`

attribute [grind] BigStep
theorem if_iff {B S T s t} : (ifThenElse B S T, s) ==>
    t ↔ (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by grind

/- Dependent pattern matching. -/

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)
@[grind =] def Vec.head : Vec α (n+1) → α
  | .cons a _ => a
example (as bs : Vec Int (n+1)) : as.head = bs.head
    → (match as, bs with
       | .cons a _, .cons b _ => a + b) = 2 * as.head := by grind

/- Theory solvers. -/

example [CommRing α] (a b c : α) :
    a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    a^4 + b^4 + c^4 = 9 := by grind

example (x : BitVec 8) : (x - 16) * (x + 16) = x^2 := by grind

example [CommSemiring α] [AddRightCancel α] (x y : α) :
    x^2*y = 1 → x*y^2 = y → y*x = 1 := by grind

example (a b : UInt32) : a ≤ 2 → b ≤ 3 → a + b ≤ 5 := by grind

example [LE α] [Std.IsLinearPreorder α] (a b c d : α) :
    a ≤ b → ¬ (c ≤ b) → ¬ (d ≤ c) → a ≤ d := by grind

/- Theory combination. -/

example [CommRing α] [NoNatZeroDivisors α]
    (a b c : α) (f : α → Nat) :
    a + b + c = 3 → a^2 + b^2 + c^2 = 5 → a^3 + b^3 + c^3 = 7 →
    f (a^4 + b^4) + f (9 - c^4) ≠ 1 := by grind

/- Interactive mode. -/

-- Remark: Mathlib contains the definition of `Real`, `sin`, and `cos`.
axiom Real : Type
instance : Lean.Grind.CommRing Real := sorry

axiom cos : Real → Real
axiom sin : Real → Real
axiom trig_identity : ∀ x, (cos x)^2 + (sin x)^2 = 1

-- Manually specify the patterns for `trig_identity`
grind_pattern trig_identity => cos x
grind_pattern trig_identity => sin x

example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind? -- Provides code action

example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind =>
    instantiate only [trig_identity]
    ring
