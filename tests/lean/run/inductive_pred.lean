import Lean 
open Lean

def checkGetBelowIndices (ctorName : Name) (indices : Array Nat) : MetaM Unit := do
  let actualIndices ← Meta.IndPredBelow.getBelowIndices ctorName
  if actualIndices != indices then
    throwError "wrong indices for {ctorName}: {actualIndices} ≟ {indices}"

namespace Ex
inductive LE : Nat → Nat → Prop
  | refl : LE n n
  | succ : LE n m → LE n m.succ
#eval checkGetBelowIndices ``LE.refl #[1]
#eval checkGetBelowIndices ``LE.succ #[1, 2, 3]

def typeOf {α : Sort u} (a : α) := α

theorem LE_brecOn : typeOf @LE.brecOn =
∀ {motive : (a a_1 : Nat) → LE a a_1 → Prop} {a a_1 : Nat} (x : LE a a_1),
  (∀ (a a_2 : Nat) (x : LE a a_2), @LE.below motive a a_2 x → motive a a_2 x) → motive a a_1 x := rfl

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
#eval checkGetBelowIndices ``Even.zero #[]
#eval checkGetBelowIndices ``Even.ss #[1, 2]

theorem Even_brecOn : typeOf @Even.brecOn = ∀ {motive : (a : Nat) → Even a → Prop} {a : Nat} (x : Even a),
  (∀ (a : Nat) (x : Even a), @Even.below motive a x → motive a x) → motive a x := rfl

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
#eval checkGetBelowIndices ``Power2.base #[]
#eval checkGetBelowIndices ``Power2.ind #[1, 2]

theorem Power2_brecOn : typeOf @Power2.brecOn = ∀ {motive : (a : Nat) → Power2 a → Prop} {a : Nat} (x : Power2 a),
  (∀ (a : Nat) (x : Power2 a), @Power2.below motive a x → motive a x) → motive a x := rfl

theorem Power2.mul : Power2 n → Power2 m → Power2 (n*m) := by
  intro h1 h2
  induction h2 with
  | base      => simp_all
  | ind h2 ih => exact mul_left_comm .. ▸ ind ih

/- The following example fails because the structural recursion cannot be performed on the `Nat`s and
   the `brecOn` construction doesn't work for inductive predicates -/
set_option trace.Elab.definition.structural true in
set_option trace.Meta.IndPredBelow.match true in
set_option pp.explicit true in
theorem Power2.mul' : Power2 n → Power2 m → Power2 (n*m)
 | h1, base => by simp_all
 | h1, ind h2 => mul_left_comm .. ▸ ind (mul' h1 h2)

inductive tm : Type :=
  | C : Nat → tm
  | P : tm → tm → tm

open tm

set_option hygiene false in
infixl:40 " ==> " => step
inductive step : tm → tm → Prop :=
  | ST_PlusConstConst : ∀ n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : ∀ t1 t1' t2,
      t1 ==> t1' →
      P t1 t2 ==> P t1' t2
  | ST_Plus2 : ∀ n1 t2 t2',
      t2 ==> t2' →
      P (C n1) t2 ==> P (C n1) t2'
#eval checkGetBelowIndices ``step.ST_PlusConstConst #[1, 2]
#eval checkGetBelowIndices ``step.ST_Plus1 #[1, 2, 3, 4]
#eval checkGetBelowIndices ``step.ST_Plus2 #[1, 2, 3, 4]

def deterministic {X : Type} (R : X → X → Prop) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

theorem step_deterministic' : deterministic step := λ x y₁ y₂ hy₁ hy₂ =>
  @step.brecOn (λ s t st => ∀ y₂, s ==> y₂ → t = y₂) _ _ hy₁ (λ s t st hy₁ y₂ hy₂ =>
    match hy₁, hy₂ with
    | step.below.ST_PlusConstConst _ _, step.ST_PlusConstConst _ _ => rfl
    | step.below.ST_Plus1 _ _ _ hy₁ ih, step.ST_Plus1 _ t₁' _ _ => by rw [←ih t₁']; assumption
    | step.below.ST_Plus1 _ _ _ hy₁ ih, step.ST_Plus2 _ _ _ _ => by cases hy₁
    | step.below.ST_Plus2 _ _ _ _ ih, step.ST_Plus2 _ _ t₂ _ => by rw [←ih t₂]; assumption
    | step.below.ST_Plus2 _ _ _ hy₁ _, step.ST_PlusConstConst _ _ => by cases hy₁
    ) y₂ hy₂

section NestedRecursion

axiom f : Nat → Nat

inductive is_nat : Nat -> Prop
| Z : is_nat 0
| S {n} : is_nat n → is_nat (f n)
#eval checkGetBelowIndices ``is_nat.Z #[]
#eval checkGetBelowIndices ``is_nat.S #[1, 2]

axiom P : Nat → Prop
axiom F0 : P 0
axiom F1 : P (f 0)
axiom FS {n : Nat} : P n → P (f (f n))

-- we would like to write this
theorem foo : ∀ {n}, is_nat n → P n
| _, is_nat.Z => F0
| _, is_nat.S is_nat.Z => F1
| _, is_nat.S (is_nat.S h) => FS (foo h)

theorem foo' : ∀ {n}, is_nat n → P n := fun h =>
  @is_nat.brecOn (fun n hn => P n) _ h fun n h ih =>
  match ih with
  | is_nat.below.Z => F0
  | is_nat.below.S is_nat.below.Z _ => F1
  | is_nat.below.S (is_nat.below.S b hx) h₂ => FS hx

end NestedRecursion

end Ex
