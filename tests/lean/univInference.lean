
universe w₁ w₂ w₃

namespace Struct
structure S1.{r, s} (α : Type s) : Type (max s r) :=
  up :: (down : α)

def ex1.{u, v} (α : Type u) (σ : Type (max v u)) (h : σ = S1.{v, u} α) : True :=
  trivial

structure S2.{u, v} (α : Sort u) (β : Sort v) :=
  (a : α)
  (b : β)

def ex2.{u, v} (α : Sort u) (β : Sort v) (σ : Sort (max u v 1)) (h : σ = S2 α β) : True :=
  trivial

structure S3.{u, v} (α : Type u) (β : Type v) :=
  (a : α)
  (b : β)

def ex3.{u, v} (α : Type u) (β : Type v) (σ : Type (max u v)) (h : σ = S3 α β) : True :=
  trivial

structure S4.{u, v} (α : Sort u) (β : Sort v) : Type _ := -- Warning: possibly too high
  (a : α)
  (b : β)

structure S5.{u, v} (α : Type (u+1)) (β : Type v) :=
  (a : α)
  (b : β)

def ex5.{u, v} (α : Type (u+1)) (β : Type v) (σ : Type (max (u+1) v)) (h : σ = S5 α β) : True :=
  trivial

structure S6.{u, v} (α : Sort (max u v)) (β : Type v) :=
  (a : α)
  (b : β)

#check S6.{w₁, w₂}

def ex6.{u, v} (α : Sort (max u v)) (β : Type v) (σ : Sort max u (v+1)) (h : σ = S6.{u, v} α β) : True :=
  trivial

structure S7.{u, v} (α : Sort u) (β : Sort v) : Sort (max u v) :=  -- Error: invalid universe polymorphic type
  (a : α) (b : β)

end Struct

namespace Induct

inductive S2.{u, v} (α : Sort u) (β : Sort v)
  | mk (a : α) (b : β)

def ex2.{u, v} (α : Sort u) (β : Sort v) (σ : Sort (max u v 1)) (h : σ = S2 α β) : True :=
  trivial

inductive S3.{u, v} (α : Type u) (β : Type v)
  | mk (a : α) (b : β)

def ex3.{u, v} (α : Type u) (β : Type v) (σ : Type (max u v)) (h : σ = S3 α β) : True :=
  trivial

inductive S4.{u, v} (α : Sort u) (β : Sort v) : Type _  -- Error: inference procedure failed
  | mk (a : α) (b : β)

inductive S5.{u, v} (α : Type (u+1)) (β : Type v)
  | mk (a : α) (b : β)

def ex5.{u, v} (α : Type (u+1)) (β : Type v) (σ : Type (max (u+1) v)) (h : σ = S5 α β) : True :=
  trivial

inductive S6.{u, v} (α : Sort u) (β : Sort v) : Sort (max u v)  -- Warning: possibly too high
  | mk (a : α) (b : β)

inductive Term
  | Var : Nat → Term
  | App : Term → Term → Term
  | All : (Nat → Term) → Term

open Lean

inductive Stx
  | node   (args : Array Stx) : Stx

def ex7 (h : Stx = Nat) : True :=
  trivial


/-!
Universe level inference failure is localized to syntax of field type.
-/
structure S8 : Type 5 where
  t1 : Sort _

/-!
Used to have an 'accidental higher universe' error.
The issue was that we would get the constraints `u ≤ ?r + 1` and `u ≤ ?r`
and it would complain about the first, despite the fact that it's implied by the second.
-/
inductive NotBadLevelConstraint (α : Sort u) (β : Type u) : Type _ where
  | mk (x : α) (y : β)

/-!
Used to have 'accidental higher universe' error.
The issue was that we would get the constraints `u ≤ ?r` and `u ≤ ?r + 1`
like in `NotBadLevelConstraint`.
-/
inductive NotBadLevelConstraint'
  | foobar {Foo : Sort u} : Foo → NotBadLevelConstraint'
  | somelist : List NotBadLevelConstraint' → NotBadLevelConstraint'

namespace Sorry
set_option warn.sorry false

/-!
Used to have an 'accidental higher universe' error.
Now there's no error. Since the resulting type is `Type`, it infers `sorry : Prop`.
-/
inductive Sorry1 where
  | y (b : sorry)

/-!
Used to have an 'invalid universe level in constructor' error.
Now there's no error. Since the resulting type is `Type`, it infers `sorry : Prop`.
-/
inductive Sorry1' : Type where
  | y (b : sorry)

/-!
Used to have an 'accidental higher universe' error.
Now has a "failed to infer universe levels in type of binder" error instead,
since the universe of `sorry` is underconstrained.
-/
inductive Sorry2 : Type 2 where
  | y (b : sorry)

end Sorry

end Induct
