abbrev f (a : α) := a

set_option grind.debug true
set_option grind.debug.proofs true

/--
error: `grind` failed
a b c : Bool
p q : Prop
left✝ : a = true
right✝ : b = true ∨ c = true
left : p
right : q
x✝ : b = false ∨ a = false
⊢ False
-/
#guard_msgs (error) in
theorem ex (h : (f a && (b || f (f c))) = true) (h' : p ∧ q) : b && a := by
  grind

open Lean.Grind.Eager in
/--
error: `grind` failed
a b c : Bool
p q : Prop
left✝ : a = true
h✝ : c = true
left : p
right : q
h : b = false
⊢ False
-/
#guard_msgs (error) in
theorem ex2 (h : (f a && (b || f (f c))) = true) (h' : p ∧ q) : b && a := by
  grind

def g (i : Nat) (j : Nat) (_ : i > j := by omega) := i + j

/--
error: `grind` failed
i j : Nat
h : j + 1 < i + 1
h✝ : j + 1 ≤ i
x✝ : ¬g (i + 1) j ⋯ = i + j + 1
⊢ False
-/
#guard_msgs (error) in
example (i j : Nat) (h : i + 1 > j + 1) : g (i+1) j = f ((fun x => x) i) + f j + 1 := by
  grind

structure Point where
  x : Nat
  y : Int

/--
error: `grind` failed
a₁ : Point
a₂ : Nat
a₃ : Int
as : List Point
b₁ : Point
bs : List Point
b₂ : Nat
b₃ : Int
head_eq : a₁ = b₁
x_eq : a₂ = b₂
y_eq : a₃ = b₃
tail_eq : as = bs
⊢ False
-/
#guard_msgs (error) in
theorem ex3 (h : a₁ :: { x := a₂, y := a₃ : Point } :: as = b₁ :: { x := b₂, y := b₃} :: bs) : False := by
  grind

def h (a : α) := a

set_option trace.grind.pre true in
example (p : Prop) (a b c : Nat) : p → a = 0 → a = b → h a = h c → a = c ∧ c = a → a = b ∧ b = a → a = c := by
  grind

set_option trace.grind.proof.detail true
set_option trace.grind.proof true
set_option trace.grind.pre true
/--
error: `grind` failed
α : Type
a : α
p q r : Prop
h₁ : HEq p a
h₂ : HEq q a
h₃ : p = r
⊢ False
-/
#guard_msgs (error) in
example (a : α) (p q r : Prop) : (h₁ : HEq p a) → (h₂ : HEq q a) → (h₃ : p = r) → False := by
  grind

example (a b : Nat) (f : Nat → Nat) : (h₁ : a = b) → (h₂ : f a ≠ f b) → False := by
  grind

example (a : α) (p q r : Prop) : (h₁ : HEq p a) → (h₂ : HEq q a) → (h₃ : p = r) → q = r := by
  grind
