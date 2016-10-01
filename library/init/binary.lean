/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

General properties of binary operations.
-/
prelude
import init.logic

universe variables u v
variable {A : Type u}
variable {B : Type v}
variable f : A → A → A
variable inv : A → A
variable one : A
local notation a * b := f a b
local notation a ⁻¹  := inv a
variable g : A → A → A
local notation a + b := g a b

def commutative        := ∀ a b, a * b = b * a
def associative        := ∀ a b c, (a * b) * c = a * (b * c)
def left_identity      := ∀ a, one * a = a
def right_identity     := ∀ a, a * one = a
def right_inverse      := ∀ a, a * a⁻¹ = one
def left_cancelative   := ∀ a b c, a * b = a * c → b = c
def right_cancelative  := ∀ a b c, a * b = c * b → a = c
def left_distributive  := ∀ a b c, a * (b + c) = a * b + a * c
def right_distributive := ∀ a b c, (a + b) * c = a * c + b * c
def right_commutative (h : B → A → B) := ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁
def left_commutative  (h : A → B → B) := ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

lemma left_comm : commutative f → associative f → left_commutative f :=
assume hcomm hassoc, take a b c, calc
  a*(b*c) = (a*b)*c  : eq.symm (hassoc a b c)
    ...   = (b*a)*c  : hcomm a b ▸ rfl
    ...   = b*(a*c)  : hassoc b a c

lemma right_comm : commutative f → associative f → right_commutative f :=
assume hcomm hassoc, take a b c, calc
  (a*b)*c = a*(b*c) : hassoc a b c
    ...   = a*(c*b) : hcomm b c ▸ rfl
    ...   = (a*c)*b : eq.symm (hassoc a c b)
