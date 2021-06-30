
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

structure S4.{u, v} (α : Sort u) (β : Sort v) : Type _ := -- Error: inference procedure failed
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

inductive S6.{u, v} (α : Sort u) (β : Sort v) : Sort (max u v)
  | mk (a : α) (b : β)

inductive Term
  | Var : Nat → Term
  | App : Term → Term → Term
  | All : (Nat → Term) → Term

inductive S7.{u, v} (α : Sort u) (β : Sort v) : Sort (max u v)  -- Error: invalid universe polymorphic type
  | mk (a : α) (b : β)

open Lean

inductive Stx
  | node   (args : Array Stx) : Stx

def ex7 (h : Stx = Nat) : True :=
  trivial

end Induct
