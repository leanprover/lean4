/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.datatypes

notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r

/-
  Global declarations of right binding strength

  If a module reassigns these, it will be incompatible with other modules that adhere to these
  conventions.

  When hovering over a symbol, use "C-c C-k" to see how to input it.
-/

definition std.prec.max   : num := 1024 -- the strength of application, identifiers, (, [, etc.
definition std.prec.arrow : num := 25

/-
The next definition is "max + 10". It can be used e.g. for postfix operations that should
be stronger than application.
-/

definition std.prec.max_plus :=
num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ
  (num.succ std.prec.max)))))))))

/- Logical operations and relations -/

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr ` ∧ `:35
reserve infixr ` /\ `:35
reserve infixr ` \/ `:30
reserve infixr ` ∨ `:30
reserve infix ` <-> `:20
reserve infix ` ↔ `:20
reserve infix ` = `:50
reserve infix ` ≠ `:50
reserve infix ` ≈ `:50
reserve infix ` ~ `:50
reserve infix ` ≡ `:50

reserve infixr ` ∘ `:60                 -- input with \comp
reserve postfix `⁻¹`:std.prec.max_plus  -- input with \sy or \-1 or \inv

reserve infixl ` ⬝ `:75
reserve infixr ` ▸ `:75
reserve infixr ` ▹ `:75

/- types and type constructors -/

reserve infixl ` ⊎ `:25
reserve infixl ` × `:30

/- arithmetic operations -/

reserve infixl ` + `:65
reserve infixl ` - `:65
reserve infixl ` * `:70
reserve infixl ` div `:70
reserve infixl ` mod `:70
reserve infixl ` / `:70
reserve prefix `-`:100
reserve infix ` ^ `:80

reserve infix ` <= `:50
reserve infix ` ≤ `:50
reserve infix ` < `:50
reserve infix ` >= `:50
reserve infix ` ≥ `:50
reserve infix ` > `:50

/- boolean operations -/

reserve infixl ` && `:70
reserve infixl ` || `:65

/- set operations -/

reserve infix ` ∈ `:50
reserve infix ` ∉ `:50
reserve infixl ` ∩ `:70
reserve infixl ` ∪ `:65
reserve infix ` ⊆ `:50
reserve infix ` ⊇ `:50

/- other symbols -/

reserve infix ` ∣ `:50
reserve infixl ` ++ `:65
reserve infixr ` :: `:65

structure has_add [class] (A : Type)  := (add : A → A → A)
structure has_mul [class] (A : Type)  := (mul : A → A → A)
structure has_inv [class] (A : Type)  := (inv : A → A)
structure has_neg [class] (A : Type)  := (neg : A → A)
structure has_sub [class] (A : Type)  := (sub : A → A → A)
structure has_division [class] (A : Type) := (division : A → A → A)
structure has_divide [class] (A : Type) := (divide : A → A → A)
structure has_modulo [class] (A : Type) := (modulo : A → A → A)
structure has_dvd [class] (A : Type)    := (dvd : A → A → Prop)
structure has_le [class] (A : Type) := (le : A → A → Prop)
structure has_lt [class] (A : Type) := (lt : A → A → Prop)

definition add {A : Type} [s : has_add A] : A → A → A := has_add.add
definition mul {A : Type} [s : has_mul A] : A → A → A := has_mul.mul
definition sub {A : Type} [s : has_sub A] : A → A → A := has_sub.sub
definition division {A : Type} [s : has_division A] : A → A → A := has_division.division
definition divide {A : Type} [s : has_divide A]   : A → A → A := has_divide.divide
definition modulo {A : Type} [s : has_modulo A]   : A → A → A := has_modulo.modulo
definition dvd {A : Type} [s : has_dvd A] : A → A → Prop := has_dvd.dvd
definition neg {A : Type} [s : has_neg A] : A → A := has_neg.neg
definition inv {A : Type} [s : has_inv A] : A → A := has_inv.inv
definition le {A : Type} [s : has_le A] : A → A → Prop := has_le.le
definition lt {A : Type} [s : has_lt A] : A → A → Prop := has_lt.lt
definition ge [reducible] {A : Type} [s : has_le A] (a b : A) : Prop := le b a
definition gt [reducible] {A : Type} [s : has_lt A] (a b : A) : Prop := lt b a

infix +    := add
infix *    := mul
infix -    := sub
infix /    := division
infix div  := divide
infix ∣    := dvd
infix mod  := modulo
prefix -   := neg
postfix ⁻¹ := inv
infix ≤    := le
infix ≥    := ge
infix <    := lt
infix >    := gt

notation [parsing-only] x ` +[`:65 A:0 `] `:0 y:65   := @add A _ x y
notation [parsing-only] x ` -[`:65 A:0 `] `:0 y:65   := @sub A _ x y
notation [parsing-only] x ` *[`:70 A:0 `] `:0 y:70   := @mul A _ x y
notation [parsing-only] x ` /[`:70 A:0 `] `:0 y:70   := @division A _ x y
notation [parsing-only] x ` div[`:70 A:0 `] `:0 y:70 := @divide A _ x y
notation [parsing-only] x ` mod[`:70 A:0 `] `:0 y:70 := @modulo A _ x y
notation [parsing-only] x ` ≤[`:50 A:0 `] `:0 y:50   := @le A _ x y
notation [parsing-only] x ` ≥[`:50 A:0 `] `:0 y:50   := @ge A _ x y
notation [parsing-only] x ` <[`:50 A:0 `] `:0 y:50   := @lt A _ x y
notation [parsing-only] x ` >[`:50 A:0 `] `:0 y:50   := @gt A _ x y
