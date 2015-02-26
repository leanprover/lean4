/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.vector
Author: Floris van Doorn, Leonardo de Moura
-/
import data.nat.basic
open nat prod

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n}, A → vector A n → vector A (succ n)

namespace vector
  notation a :: b := cons a b
  notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

  variables {A B C : Type}

  protected definition is_inhabited [instance] [h : inhabited A] : ∀ (n : nat), inhabited (vector A n)
  | is_inhabited 0     := inhabited.mk nil
  | is_inhabited (n+1) := inhabited.mk (inhabited.value h :: inhabited.value (is_inhabited n))

  theorem vector0_eq_nil : ∀ (v : vector A 0), v = nil
  | vector0_eq_nil nil := rfl

  definition head : Π {n : nat}, vector A (succ n) → A
  | head (a::v) := a

  definition tail : Π {n : nat}, vector A (succ n) → vector A n
  | tail (a::v) := v

  theorem head_cons {n : nat} (h : A) (t : vector A n) : head (h :: t) = h :=
  rfl

  theorem tail_cons {n : nat} (h : A) (t : vector A n) : tail (h :: t) = t :=
  rfl

  theorem eta : ∀ {n : nat} (v : vector A (succ n)), head v :: tail v = v
  | eta (a::v) := rfl

  definition last : Π {n : nat}, vector A (succ n) → A
  | last (a::nil) := a
  | last (a::v)   := last v

  theorem last_singleton (a : A) : last (a :: nil) = a :=
  rfl

  theorem last_cons {n : nat} (a : A) (v : vector A (succ n)) : last (a :: v) = last v :=
  rfl

  definition const : Π (n : nat), A → vector A n
  | const 0        a := nil
  | const (succ n) a := a :: const n a

  theorem head_const (n : nat) (a : A) : head (const (succ n) a) = a :=
  rfl

  theorem last_const : ∀ (n : nat) (a : A), last (const (succ n) a) = a
  | last_const 0        a := rfl
  | last_const (succ n) a := last_const n a

  definition map (f : A → B) : Π {n : nat}, vector A n → vector B n
  | map nil    := nil
  | map (a::v) := f a :: map v

  theorem map_nil (f : A → B) : map f nil = nil :=
  rfl

  theorem map_cons {n : nat} (f : A → B) (h : A) (t : vector A n) : map f (h :: t) =  f h :: map f t :=
  rfl

  definition map2 (f : A → B → C) : Π {n : nat}, vector A n → vector B n → vector C n
  | map2 nil     nil     := nil
  | map2 (a::va) (b::vb) := f a b :: map2 va vb

  theorem map2_nil (f : A → B → C) : map2 f nil nil = nil :=
  rfl

  theorem map2_cons {n : nat} (f : A → B → C) (h₁ : A) (h₂ : B) (t₁ : vector A n) (t₂ : vector B n) :
                    map2 f (h₁ :: t₁) (h₂ :: t₂) = f h₁ h₂ :: map2 f t₁ t₂ :=
  rfl

  -- Remark: why do we need to provide indices?
  definition append : Π {n m : nat}, vector A n → vector A m → vector A (n ⊕ m)
  | @append 0        m nil    w := w
  | @append (succ n) m (a::v) w := a :: (append v w)

  theorem append_nil {n : nat} (v : vector A n) : append nil v = v :=
  rfl

  theorem append_cons {n m : nat} (h : A) (t : vector A n) (v : vector A m) :
    append (h::t) v = h :: (append t v) :=
  rfl

  definition unzip : Π {n : nat}, vector (A × B) n → vector A n × vector B n
  | unzip nil           := (nil, nil)
  | unzip ((a, b) :: v) := (a :: pr₁ (unzip v), b :: pr₂ (unzip v))

  theorem unzip_nil : unzip (@nil (A × B)) = (nil, nil) :=
  rfl

  theorem unzip_cons {n : nat} (a : A) (b : B) (v : vector (A × B) n) :
       unzip ((a, b) :: v) = (a :: pr₁ (unzip v), b :: pr₂ (unzip v)) :=
  rfl

  definition zip : Π {n : nat}, vector A n → vector B n → vector (A × B) n
  | zip nil     nil     := nil
  | zip (a::va) (b::vb) := ((a, b) :: zip va vb)

  theorem zip_nil_nil : zip (@nil A) (@nil B) = nil :=
  rfl

  theorem zip_cons_cons {n : nat} (a : A) (b : B) (va : vector A n) (vb : vector B n) :
      zip (a::va) (b::vb) = ((a, b) :: zip va vb) :=
  rfl

  theorem unzip_zip : ∀ {n : nat} (v₁ : vector A n) (v₂ : vector B n), unzip (zip v₁ v₂) = (v₁, v₂)
  | @unzip_zip 0        nil     nil     := rfl
  | @unzip_zip (succ n) (a::va) (b::vb) := calc
       unzip (zip (a :: va) (b :: vb))
             = (a :: pr₁ (unzip (zip va vb)), b :: pr₂ (unzip (zip va vb))) : rfl
        ...  = (a :: pr₁ (va, vb), b :: pr₂ (va, vb))                       : {unzip_zip va vb}
        ...  = (a :: va, b :: vb)                                           : rfl

  theorem zip_unzip : ∀ {n : nat} (v : vector (A × B) n), zip (pr₁ (unzip v)) (pr₂ (unzip v)) = v
  | @zip_unzip 0        nil            := rfl
  | @zip_unzip (succ n) ((a, b) :: v)  := calc
    zip (pr₁ (unzip ((a, b) :: v))) (pr₂ (unzip ((a, b) :: v)))
         = (a, b) :: zip (pr₁ (unzip v)) (pr₂ (unzip v)) : rfl
     ... = (a, b) :: v                                   : {zip_unzip v}

  /- Concat -/

  definition concat : Π {n : nat}, vector A n → A → vector A (succ n)
  | concat nil    a := a :: nil
  | concat (b::v) a := b :: concat v a

  theorem concat_nil (a : A) : concat nil a = a :: nil :=
  rfl

  theorem concat_cons {n : nat} (b : A) (v : vector A n) (a : A) : concat (b :: v) a = b :: concat v a :=
  rfl

  theorem last_concat : ∀ {n : nat} (v : vector A n) (a : A), last (concat v a) = a
  | @last_concat 0        nil    a := rfl
  | @last_concat (succ n) (b::v) a := calc
    last (concat (b::v) a) = last (concat v a) : rfl
                    ...    = a                 : last_concat v a
end vector
