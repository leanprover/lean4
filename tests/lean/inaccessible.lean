universe variables u v
inductive imf {A : Type u} {B : Type v} (f : A → B) : B → Type (max 1 u v)
| mk : ∀ (a : A), imf (f a)

definition inv_1 {A : Type u} {B : Type v} (f : A → B) : ∀ (b : B), imf f b → A
| .(f a) (imf.mk .(f) a)  := a

definition inv_2 {A : Type u} {B : Type v} (f : A → B) : ∀ (b : B), imf f b → A
| ._ (imf.mk ._ a)  := a

definition mk {A : Type u} {B : Type v} {f : A → B} (a : A) := imf.mk f a

definition inv_3 {A : Type u} {B : Type v} (f : A → B) : ∀ (b : B), imf f b → A
| .(f a) (mk a)  := a -- Error, mk is not a constructor

definition inv_4 {A : Type u} {B : Type v} (f : A → B) : ∀ (b : B), imf f b → A
| .(f a) (.(mk) a)  := a -- Error, we cannot use inaccessible annotation around functions in applications

attribute [pattern] mk

definition inv_5 {A : Type u} {B : Type v} (f : A → B) : ∀ (b : B), imf f b → A
| .(f a) (mk a)  := a

definition inv_6 {A : Type u} {B : Type v} (f : A → B) : ∀ (b : B), imf f b → A
| (f a) (mk a)  := a  -- Error, 'a' is being "declared" twice in the pattern

definition inv_7 {A : Type u} {B : Type v} (f : A → B) : ∀ (b : B), imf f b → A
| (f a) (mk b)  := a  -- Typing error, it would also fail when compiling the pattern

definition g_1 : nat → nat → nat
| a a := a   -- Error, 'a' is being "declared" twice

definition g_2 (a : nat) : nat → nat → nat
| a b := a

example (a b c : nat) : g_2 a b c = b :=
rfl

inductive vec1 (A : Type u) : nat → Type (max 1 u)
| nil  : vec1 0
| cons : ∀ n, A → vec1 n → vec1 (n+1)

section
open vec1

definition map_1 {A : Type u} (f : A → A → A) : Π {n}, vec1 A n → vec1 A n → vec1 A n
| 0     (nil .(A))        (nil .(A))        := nil A
| (n+1) (cons .(n) h₁ v₁) (cons .(n) h₂ v₂) := cons n (f h₁ h₂) (map_1 v₁ v₂)

definition map_2 {A : Type u} (f : A → A → A) : Π {n}, vec1 A n → vec1 A n → vec1 A n
| 0     (nil ._)        (nil ._)        := nil A
| (n+1) (cons ._ h₁ v₁) (cons ._ h₂ v₂) := cons n (f h₁ h₂) (map_2 v₁ v₂)

/- In map_3, we use the inaccessible terms to avoid pattern/matching on the first argument -/
definition map_3 {A : Type u} (f : A → A → A) : Π {n}, vec1 A n → vec1 A n → vec1 A n
| ._ (nil ._)      (nil ._)        := nil A
| ._ (cons n h₁ v₁) (cons .(n) h₂ v₂) := cons n (f h₁ h₂) (map_3 v₁ v₂)
end

inductive vec2 (A : Type u) : nat → Type (max 1 u)
| nil {} : vec2 0
| cons   : ∀ {n}, A → vec2 n → vec2 (n+1)

section
open vec2

definition map_4 {A : Type u} (f : A → A → A) : Π {n}, vec2 A n → vec2 A n → vec2 A n
| 0     nil          nil          := nil
| (n+1) (cons h₁ v₁) (cons h₂ v₂) := cons (f h₁ h₂) (map_4 v₁ v₂)

definition map_5 {A : Type u} (f : A → A → A) : Π {n}, vec2 A n → vec2 A n → vec2 A n
| ._  nil          nil         := nil
| ._ (@cons ._ n h₁ v₁) (cons h₂ v₂) := cons (f h₁ h₂) (map_5 v₁ v₂)

/-
The following variant will be rejected by the new equation compiler.
In Lean2, the second equation is accepted because unassigned metavariables
occurring in patterns become new variables. This feature is too hackish.
-/
definition map_6 {A : Type u} (f : A → A → A) : Π {n}, vec2 A n → vec2 A n → vec2 A n
| ._  nil          nil         := nil
| ._ (cons h₁ v₁) (cons h₂ v₂) := cons (f h₁ h₂) (map_6 v₁ v₂)
end
