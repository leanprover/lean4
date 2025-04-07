/-
Copyright (c) 2024 Marcus Rossel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rossel, Kim Morrison
-/
import Lean.Elab.Term
set_option grind.warning false
/-!
These tests are originally from the `lean-egg` repository at
https://github.com/marcusrossel/lean-egg and were written by Marcus Rossel.

They are re-used here with permission, and adapted as regression tests for the `grind` tactic.
-/

section

example (p q : Nat → Prop) : ((∀ x, p x) ∧ (∀ x, q x)) ↔ ∀ x, p x ∧ q x := by
  grind

example (p q : Nat → Nat → Prop) : ((∀ x, p 1 x) ∧ (∀ x, q 1 x)) ↔ ∀ x, p 1 x ∧ q 1 x := by
  grind

example (p q : Nat → Nat → Prop) : ((∀ x, p x 1) ∧ (∀ x, q x 1)) ↔ ∀ x, p x 1 ∧ q x 1 := by
  grind

example (p q : Nat → Nat → Prop) : ((∀ x, p x 1) ∧ (∀ x, q x 1)) ↔ ∀ x, p x 1 ∧ q x 1 := by
  grind

end

section

example : (fun x => x) 0 = 0 := by
  grind

example : (fun _ => 1) 0 = 1 := by
  grind

example : (fun x => (fun y => y) x) 0 = 0 := by
  grind

example : (fun x => (fun _ => x) x) 0 = 0 := by
  grind

example : (fun x => (fun _ => x) 0) 1 = 1 := by
  grind

example : id ((fun x => x + 1) 2) = id (2 + 1) := by
  grind

example (h : y + 1 = z) : (fun _ => y + 1) 0 = z := by
  grind

example (h : y + 1 = z) : (fun x => x + 1) y = z := by
  grind

end

section

example :
    (∀ (α : Type) (l : List α), l.length = l.length) ↔
    (∀ (α : Type) (l : List α), l.length = l.length) := by
  grind

end

section

example (h₁ : x ∧ y) (h₂ : x ∧ y → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : x ∧ y) (h₂ : x ∧ y → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : x ∧ y) (h₂ : y ∧ x → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : x ∧ y) (h₂ : y ∧ x → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : x ∧ y) (h₂ : y ∧ x → 1 = 2) : 1 = 2 := by
  grind

example {a : Nat} (h : a < b) : a % b = a := by
  grind only [Nat.mod_eq_of_lt]

example {x : Nat} (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  grind

example {x : Nat} (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  grind

example {x : Nat} (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  grind

example (h : ∀ p : Prop, p → 1 = id 1) : 1 = id 1 := by
  grind only [id]

example (h : ∀ p : Prop, p → (1 : Int) = id 1) : (1 : Int) = id 1 := by
  grind only [id]

example {p q r : Prop} (h₁ : p) (h₂ : p ↔ q) (h₃ : q → (p ↔ r)) : p ↔ r := by
  grind

example {p q r : Prop} (h₁ : p) (h₂ : p ↔ q) (h₃ : q ↔ r) (h₄ : r → (p ↔ s)) : p ↔ s := by
  grind

end

section

example (h : 0 = 0 → 1 = 2) : 1 = 2 := by
  grind

example (h : (0 = (fun x => x) 0) → 1 = 2) : 1 = 2 := by
  grind

variable {x : Nat} {f : Nat → Nat}

example (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : x = y) (h₂ : y = z) (h₃ : x = z → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : ∀ a : Nat, f a = a) (h₂ : f x = x → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : ∀ a : Nat, f a = a) (h₂ : p ∧ q) (h₃ : (f x = x) → (p ∧ q) → 1 = 2) : 1 = 2 := by
  grind

example (h₁ : ∀ a : Nat, f a = a) (h₂ : p ∧ q) (h₃ : p ∧ q ↔ r) (h₄ : (f x = x) → r → 1 = 2) :
    1 = 2 := by
  grind

end

section

example : (fun _ => 1) 0 = 1 := by
  grind

end

section

example : (fun (z : α → α → α) x => (fun _y => z) x x) = (fun x => x) := by
  grind

end

section

example : (fun x => Nat.succ x) = Nat.succ := by
  grind

example : id (fun x => Nat.succ x) = id Nat.succ := by
  grind

example : (fun x => Nat.succ x) x = Nat.succ x := by
  grind

example (f : Nat → Nat) (h : f = g) : (fun x : Nat => f x) y = g y := by
  grind

example (f : Nat → Nat) (h : f y = g) : (fun x : Nat => f x) y = g := by
  grind

elab "eta" n:num fn:ident ty:term : term => open Lean.Elab.Term in do
  let rec go (n : Nat) :=
    if n = 0
    then elabTerm fn none
    else return .lam `x (← elabTerm ty none) (.app (← go <| n - 1) (.bvar 0)) .default
  go n.getNat

example : (eta 2 Nat.succ Nat) = Nat.succ := by
  grind

example : (eta 2 Nat.succ Nat) x = Nat.succ x := by
  grind

example : id (eta 2 Nat.succ Nat) = id Nat.succ := by
  grind

example : (eta 50 Nat.succ Nat) = Nat.succ := by
  grind

example (f : α → α → α → α) : (fun a b => (fun x => (f a b) x)) = (fun a b => f a b) := by
  grind

end

section

example : true = true := by
  grind

example (h : true = false) : true = false := by
  grind

variable (f : Nat → Nat → Nat)

example (h : ∀ x y : Nat, f x y = f y x) : f 1 2 = f 2 1 := by
  grind

example (a b : Nat) (h : ∀ x y : Nat, f x y = f y x) : f a b = f b a := by
  grind

example (a b : Nat) (h : ∀ x y : Nat, f x x = f y x) : f a a = f b a := by
  grind

end

section

namespace Functional

inductive List α
  | nil : List α
  | cons : α → List α → List α

def append : List α → List α → List α
  | .nil,       bs => bs
  | .cons a as, bs => .cons a (append as bs)

theorem append_nil (as : List α) : append as .nil = as := by
  induction as with
  | nil         => grind only [append]
  | cons _ _ ih => grind only [append]

theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
  induction as with
  | nil         => grind only [append]
  | cons _ _ ih => grind only [append]

def reverseAux : List α → List α → List α
  | .nil,      r => r
  | .cons a l, r => reverseAux l (.cons a r)

def reverse (as : List α) : List α :=
  reverseAux as .nil

theorem reverseAux_eq_append (as bs : List α) :
    reverseAux as bs = append (reverseAux as .nil) bs := by
  induction as generalizing bs with
  | nil         => grind only [reverseAux, append]
  | cons _ _ ih => grind only [reverseAux, append_assoc, append]

theorem reverse_nil : reverse (.nil : List α) = .nil := by
  grind only [reverse, reverseAux]

theorem reverse_cons (a : α) (as : List α) :
    reverse (.cons a as) = append (reverse as) (.cons a .nil) := by
  grind only [reverse, reverseAux, reverseAux_eq_append]

theorem reverse_append (as bs : List α) :
    reverse (append as bs) = append (reverse bs) (reverse as) := by
  induction as generalizing bs with
  | nil          => grind only [reverse_nil, append_nil, append]
  | cons a as ih => grind only [append_assoc, reverse_cons, append]

def map (f : α → β) : List α → List β
  | .nil       => .nil
  | .cons a as => .cons (f a) (map f as)

def foldr (f : α → β → β) (init : β) : List α → β
  | .nil      => init
  | .cons a l => f a (foldr f init l)

def all (p : α → Bool) (xs : List α) : Bool :=
  foldr and true (map p xs)

def all' (p : α → Bool) : List α → Bool
  | .nil       => true
  | .cons x xs => (p x) && (all' p xs)

theorem all_deforestation (p : α → Bool) (xs : List α) : all p xs = all' p xs := by
  induction xs with
  | nil         => grind only [all, all', foldr, map]
  | cons _ _ ih => grind only [all, all', foldr, map]

end Functional

end

section

example (h₁ : ∀ p, p ∧ p) (h₂ : (∀ p, p ∧ p) → q = True) : q = True := by
  grind

end

section

example (a b : Nat) : a + b = b + a := by
  have h := Nat.add_comm
  grind

example (a : Nat) : (∀ x, x + 1 = 1 + x) → a + 1 = 1 + a :=
  fun h => by grind

example (a : Nat) : (∀ x, x + 1 = 1 + x) → a + 1 = 1 + a := by
  grind

example (a : Nat) : a + 1 = 1 + a := by
  grind

example (a : Nat) : (∀ x, x + 1 = 1 + x) → a + 1 = 1 + a :=
  fun _ => by grind

variable (h : ∀ x, x + 1 = 1 + x) in
example (a : Nat) : a + 1 = 1 + a := by
  grind

variable {h : ∀ x, x + 1 = 1 + x} in
example (a : Nat) : a + 1 = 1 + a := by
  grind

end

section

example : Nat → (x : Nat) → x = x := by
  intro x
  grind

example : Nat → (x : Nat) → (x_1 : Nat) → x = x := by
  intro x_1
  grind

end

section

example (f : α → γ) (g : β → δ) : List.map (Prod.map f g) [] = [] := by
  grind only [List.map]

example (f : α → γ) (g : β → δ) : List.map (Prod.map f g) [] = [] := by
  grind only [List.map]

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

example (f : α → γ) (g : β → δ) : List.map (Prod.map f g) [] = [] := by
  grind only [List.map]

example (f : α → γ) (g : β → δ) : List.map (Prod.map f g) [] = [] := by
  grind only [List.map]

-- This example requires `Level.succ (Level.max _ _) = Level.max (Level.succ _) (Level.succ _)`.
example (h : ∀ γ : Type (max u v), γ = id γ) (α : Type u) (β : Type v) : (α × β) = id (α × β) := by
  grind

end

section

example : 0 = Nat.zero := by
  grind

example : 1 = Nat.succ 0 := by
  grind

example : Nat.succ 1 = Nat.succ (Nat.succ Nat.zero) := by
  grind

example : Int.ofNat (Nat.succ 1) = Int.ofNat (Nat.succ (Nat.succ Nat.zero)) := by
  grind

example (h : ∀ n, Nat.succ n = n + 1) : 1 = Nat.zero + 1 := by
  grind

example : 1 = Nat.zero + 1 := by
  grind

elab "app" n:num fn:ident arg:term : term => open Lean.Elab.Term in do
  let fn ← elabTerm fn none
  let rec go (n : Nat) := if n = 0 then elabTerm arg none else return .app fn <| ← go (n - 1)
  go n.getNat

example : (app 80 Nat.succ (nat_lit 0)) = (nat_lit 80) := by grind

example : 12345 + 67890 = 80235 := by
  grind

example : 12345 - 67890 = 0 := by
  grind

example : 67890 - 12345 = 55545 := by
  grind

example : 12345 * 67890 = 838102050 := by
  grind

example : 1234 ^ 5 = 2861381721051424 := by
  grind

example : 12345 / 67890 = 0 := by
  grind

example : 67890 / 12345 = 5 := by
  grind

example : 12345 / 0 = 0 := by
  grind

example : 67890 % 12345 = 6165 := by
  grind

example : 12345 % 67890 = 12345 := by
  grind

example : 12345 % 0 = 12345 := by
  grind

end

section

example (h : (a = b) ↔ (c = d)) : 0 = 0 := by
  grind

example (h₁ : (a = b) ↔ (c = d)) (h₂ : a = b) : c = d := by
  grind

example (h₁ : (a = b) ↔ (c = d)) (h₂ : a = b) : c = d := by
  grind

example (h₁ : (a = b) ↔ (c = d)) (h₂ : c = d) : a = b := by
  grind

example (h₁ : (a = b) ↔ (c = d)) (h₂ : a = b) (h₃ : d = e) : c = e := by
  grind

end

section

variable {I : Type u} {f : I → Type v₁} (x y : (i : I) → f i) (i : I)

instance instMul [∀ i, Mul <| f i] : Mul (∀ i : I, f i) :=
  ⟨fun f g i => f i * g i⟩

theorem mul_apply [∀ i, Mul <| f i] : (x * y) i = x i * y i :=
  rfl

example : True = True := by
  grind only [mul_apply]

end

section

variable (h : ∀ (p : Nat → Nat) (x : Nat), p x = p (x + 0))

example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  grind

example (f : Nat → Nat → Nat) : (f (nat_lit 1)) x = (f 1) (x + 0) := by
  grind

example (f : Nat → Nat → Nat) : (f 1) x = (f (nat_lit 1)) (x + 0) := by
  grind

example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + (nat_lit 0)) := by
  grind

example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  grind

example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  grind

end

section

example : ([] : List α) = [] := by
  grind

example {l₁ l₂ : List α} : l₁ ++ l₂ = (l₂.reverse ++ l₁.reverse).reverse := by
  grind only [List.reverse_append, List.reverse_reverse]

end

section

example : True := by
  grind

example : True ↔ True := by
  grind

example (p q : Prop) (h : p ↔ q) : p ↔ q := by
  grind

example (x : Nat) : (x.add (.succ .zero) = x) ↔ ((Nat.succ .zero).add x = x) := by
  have h (x y : Nat) : x.add y = y.add x := Nat.add_comm ..
  grind

example (h : False) : False := by
  grind

example {p q r : Prop} (h₁ : p ∧ q) (h₂ : p ∧ q → r) : r := by
  grind

example (h : True) : True := by
  grind

example (h : 0 = 0) : 0 = 0 := by
  grind

example (a b : Nat) (h : a = b) : a = b := by
  grind

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  grind

example (h : p ∧ q ∧ r) : r ∧ r ∧ q ∧ p ∧ q ∧ r ∧ p := by
  grind

example (P : Nat → Prop) (hp : P Nat.zero.succ) (h : ∀ n, P n ↔ P n.succ) :
    P Nat.zero.succ.succ.succ.succ := by
  grind

end

section

example : 0 = 0 := by
  grind

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  grind

open List in
example (as bs : List α) : reverse (as ++ bs) = (reverse bs) ++ (reverse as) := by
  induction as generalizing bs with
  | nil  => grind only [reverse_nil, append_nil, List.nil_append]
  | cons => grind only [append_assoc, reverse_cons, List.cons_append]

variable (a b c d : Int)

example {p q r : Prop} (h₁ : p) (h₂ : p ↔ q) (h₃ : q → (p ↔ r)) : p ↔ r := by
  grind

end

section

example (arr : Array α) (i : Nat) (h₁ h₂ : i < arr.size) : arr[i]'h₁ = arr[i]'h₂ := by
  grind

end

section

example : true = true := by
  grind

example : True → true = true := by
  grind

example : True → False → true = true := by
  grind

abbrev P := ∀ x y : Nat, x + y = x + y

example : P := by
  grind

abbrev R := true = false

example (h : R) : true = false := by
  grind

abbrev S := ∀ _ : 0 = 0, R

example (h : S) : R := by
  grind

end

section

example : (fun x => (fun t _y => t) (fun z => x z)) = (fun (x : α → α) (_y : α) => x) := by
  grind

end

section

example : 0 = Nat.zero := by
  grind

example : 1 = Nat.succ 0 := by
  grind

example : Nat.succ 1 = Nat.succ (Nat.succ Nat.zero) := by
  grind

example : Int.ofNat (Nat.succ 1) = Int.ofNat (Nat.succ (Nat.succ Nat.zero)) := by
  grind

example (h : ∀ n, Nat.succ n = n + 1) : 1 = Nat.zero + 1 := by
  grind

end

section

example : "a" = "a" := by
  grind

example : "a\nb" = "a\nb" := by
  grind

example : "" = "" := by
  grind

example : " " = " " := by
  grind

example : "a b" = "a b" := by
  grind

example : "(" = "(" := by
  grind

example : ")" = ")" := by
  grind

example (h : "Le " ++ " an" = "Le  an") : "Le " ++ " an" = "Le  an" := by
  grind

end

section

class Inv (α) where inv : α → α
postfix:max "⁻¹" => Inv.inv

class Group (α) extends Mul α, One α, Inv α where
  mul_assoc    (a b c : α) : (a * b) * c = a * (b * c)
  one_mul      (a : α)     : 1 * a = a
  mul_one      (a : α)     : a * 1 = a
  inv_mul_self (a : α)     : a⁻¹ * a = 1
  mul_inv_self (a : α)     : a * a⁻¹ = 1

variable [Group α] (a b x y : α)

attribute [grind _=_] Group.mul_assoc
attribute [grind] Group.one_mul
attribute [grind] Group.mul_one
attribute [grind] Group.inv_mul_self
attribute [grind] Group.mul_inv_self

example : a⁻¹ * (a * b) = b := by grind

@[grind]
theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by grind

@[grind]
theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by grind

end

section

example (h : ∀ [inst : Neg Int] (x : Int), @Neg.neg Int inst x = x) : (0 : Int) = (0 : Int) := by
  grind

example (h : ∀ [inst : Neg Int] (x : Int), @Neg.neg Int inst x = x) : (0 : Int) = (0 : Int) := by
  grind

example (h : ∀ (α) [inst : Neg α] (x : α), @Neg.neg α inst x = x) : (0 : Int) = (0 : Int) := by
  grind

end

section -- from `TC Proj Binders.lean`

example (h : (fun (α) [Mul α] (x y : α) => x * y) = a) : true = true := by
  grind

example (x : Nat) (h : ∀ (_ : x * y = z), z = z) : x = x := by
  grind

end

section -- from `TC Stuck.lean`

def f [Inhabited α] : α := Inhabited.default

example : 0 = 0 := by
  grind only [f]

end

section -- (failing tests) from `Thomas.lean`

example :
    ((fun x => (fun t (_y : α) => t) (fun z => x z)) (fun (z : α → α → α) x => ((fun _y => z) x) x))
    = fun _y => (fun z => z) := by
  grind

example :
    ((fun x => (fun t (_y : α) => t) (fun z => x z)) (fun (z : α → α → α) x => ((fun _y => z) x) x))
    = fun _y => (fun z => z) := by
  grind

end

section

variable (h : True ↔ ∀ (a : Nat) (_ : a > 0), True)

example : True ↔ ∀ (a : Nat) (_ : a > 0), True := by
  grind

end

section -- (failing test) from `WIP AC.lean`

example {a b c d e f g h i j k l m n o p q r s t u v w x y z : Nat} :
    a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r + s + t + u + v + w + x + y + z =
    z + y + x + w + v + u + t + s + r + q + p + o + n + m + l + k + j + i + h + g + f + e + d + c + b + a := by
  grind

end
