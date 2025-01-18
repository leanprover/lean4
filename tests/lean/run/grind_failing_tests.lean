import Lean.Elab.Term

section

def f : Nat → Nat
  | .zero   => .zero
  | .succ n => f n

def g : Nat → Nat
  | .zero   => .zero
  | .succ n => g n

example : f (g Nat.zero.succ.succ) = .zero := by
  grind [f, g]

end

section

namespace Simple

class C (α) extends NatCast α, Add α

variable (cast_add : ∀ {R} [C R] (m n : Nat), ((m + n : Nat) : R) = m + n)

include cast_add in
example (a b : Nat) [C R] : Nat.cast (a + b) = (a : R) + b := by
  grind

instance : C Int where

include cast_add in
example (a b : Nat) : Nat.cast (a + b) = (a : Int) + b := by
  grind

end Simple

namespace NoDiamond

class N (R) extends NatCast R, Add R where

variable (cast_add : ∀ {R : Type _} [N R] (m n : Nat), ((m + n : Nat) : R) = m + n)

include cast_add in
example (a b : Nat) [N R] : Nat.cast (a + b) = (a : R) + b := by
  grind

instance : N Int where

include cast_add in
example (a b : Nat) : Nat.cast (a + b) = (a : Int) + b := by
  grind

end NoDiamond

namespace Diamond

class A (α) extends Add α where
class B (α) extends Add α where
class N (R) extends NatCast R, A R, B R where

variable (cast_add : ∀ {R} [N R] (m n : Nat), ((m + n : Nat) : R) = m + n)

include cast_add in
example (a b : Nat) [N R] : Nat.cast (a + b) = (a : R) + b := by
  grind

instance : N Int where

include cast_add in
example (a b : Nat) : Nat.cast (a + b) = (a : Int) + b := by
  grind

end Diamond

end

section

def Mul.pow [Mul α] [OfNat α 1] (a : α) : Nat → α
  | 0     => 1
  | n + 1 => a * (pow a n)

instance mulPow [Mul α] [OfNat α 1] : Pow α Nat where
  pow := Mul.pow

example [Mul α] [OfNat α 1] (a : α) : Mul.pow a 0 = (1 : α) := by
  grind [Mul.pow]

example [Mul α] [OfNat α 1] (a : α) : a ^ 0 = (1 : α) := by
  grind [Mul.pow]

end

section

example (h : Nat → 0 = 1) : 0 = 1 := by
  grind

end

section

axiom ax : 1 = 2

example : 1 = 2 := by
  grind [ax]

end

section

example (a : Nat) (b : Nat → False) : False := by grind -- fails

example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  grind

example : (fun x => x) = Add.add 0 := by
  grind

end

section

-- We probably don't want to support this, it requires aggressive instantiation.
example [Mul G] (h : ∀ x y z w : G, x * y = (z * w) * w) : ∀ x y z w : G, x * y = z * w := by
  grind

end

section

-- We probably don't want to support these, it requires aggressive instantiation.

variable (f : Nat → Nat → Nat)

example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  grind

example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  grind

example (a : Nat) (h₁ : ∀ x : Nat, 0 = f x x) (h₂ : ∀ x : Nat, 1 = f x x) : 0 = 1 := by
  grind

end

section

elab "app" n:num fn:ident arg:term : term => open Lean.Elab.Term in do
  let fn ← elabTerm fn none
  let rec go (n : Nat) := if n = 0 then elabTerm arg none else return .app fn <| ← go (n - 1)
  go n.getNat

example : (app 80 Nat.succ (nat_lit 0)) = (nat_lit 80) := by grind

example (f : Nat → Nat) (h : ∀ x, f x = x.succ) : 30 = app 30 f 0 := by
  grind


example (h : ∀ f : Nat → Nat, f (1 + 1) = x) : id 2 = x := by
  grind

example (h : ∀ f : Nat → Nat, f (3 - 2) = x) : id 1 = x := by
  grind

example (h : ∀ f : Nat → Nat, f (2 * 3) = x) : id 6 = x := by
  grind

example (h : ∀ f : Nat → Nat, f (4 / 2) = x) : id 2 = x := by
  grind

example (h : ∀ f : Nat → Nat, f (5 % 3) = x) : id 2 = x := by
  grind

example (h : ∀ f : Nat → Nat, f (2 ^ 3) = x) : id 8 = x := by
  grind

end

section

def f' : Bool → Nat
  | false => 0
  | true => 1

example : f' false = 0 := by
  grind [f']

end

section

-- attribute [grind _=_] List.append_eq -- needs this to work currently

open List in
example (as bs : List α) : reverse (as ++ bs) = (reverse bs) ++ (reverse as) := by
  induction as generalizing bs with
  | nil  => grind [reverse_nil, append_nil, List.append]
  | cons => grind [append_assoc, reverse_cons, List.append]

end

section

example (f i : Nat → Nat → Nat) (h₁ : f y = g) (h₂ : g y = i y (nat_lit 0)) :
    (f ·) y y = (i ·) y (nat_lit 0) := by
  grind

example (f i : Nat → Nat → Nat) (h₁ : f y = g) (h₂ : g y = i y (nat_lit 0)) :
    (i ·) y (nat_lit 0) = (f ·) y y := by
  grind

end

section

abbrev Q := ∀ x : Nat, x = nat_lit 0

-- Checks that we can "see through" definitions in rewrites where the body is an equality.
example (h : Q) : 1 = 0 := by
  grind


end

section

variable
  {n : Nat} {p : Nat → Prop} [inst : DecidablePred p]
  {find : [DecidablePred p] → (∃ n, p n) → Nat}
  {find_lt_iff : ∀ (h : ∃ y : Nat, p y) (n : Nat), find h < n ↔ ∃ m < n, p m}

include find_lt_iff in
theorem find_le_iff (h : ∃ z : Nat, p z) (n : Nat) : find h ≤ n ↔ ∃ m ≤ n, p m := by
  grind

end

section

example [inst : Decidable p] (h : [Decidable p] → p = q) : p = q := by
  grind

end

-- From `Zulip.lean`
section

variable {α} {f : α → α → α} (f_comm : ∀ a b, f a b = f b a) (f_assoc : ∀ a b c, f (f a b) c = f a (f b c))

include f_assoc f_comm in
theorem foldl_descend : (head :: tail).foldl f init = f init (tail.foldl f head) := by
  induction tail generalizing init <;> grind [List.foldl]

include f_assoc f_comm in
theorem foldl_eq_foldr (l : List α) : l.foldl f init = l.foldr f init := by
  induction l <;> grind [List.foldl, List.foldr, foldl_descend]

end
