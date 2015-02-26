/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.reserved_notation
Authors: Leonardo de Moura

Basic datatypes
-/

prelude
import init.datatypes

notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r

/-
  Global declarations of right binding strength

  If a module reassigns these, it will be incompatible with other modules that adhere to these
  conventions.

  When hovering over a symbol, use "C-u C-x =" to see how to input it.
-/

/- Logical operations and relations -/

definition std.prec.max   : num := 1024 -- reflects max precedence used internally
definition std.prec.arrow : num := 25

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr `∧`:35
reserve infixr `/\`:35
reserve infixr `\/`:30
reserve infixr `∨`:30
reserve infix `<->`:25
reserve infix `↔`:25
reserve infix `=`:50
reserve infix `≠`:50
reserve infix `≈`:50
reserve infix `∼`:50

reserve infixr `∘`:60      -- input with \comp
reserve postfix `⁻¹`:100  --input with \sy or \-1 or \inv
reserve infixl `⬝`:75
reserve infixr `▸`:75

/- types and type constructors -/

reserve infixr `⊎`:25
reserve infixr `×`:30

/- arithmetic operations -/

reserve infixl `+`:65
reserve infixl `-`:65
reserve infixl `*`:70
reserve infixl `div`:70
reserve infixl `mod`:70
reserve infixl `/`:70
reserve prefix `-`:100

reserve infix `<=`:50
reserve infix `≤`:50
reserve infix `<`:50
reserve infix `>=`:50
reserve infix `≥`:50
reserve infix `>`:50

/- boolean operations -/

reserve infixl `&&`:70
reserve infixl `||`:65

/- set operations -/

reserve infix `∈`:50
reserve infix `∉`:50
reserve infixl `∩`:70
reserve infixl `∪`:65

/- other symbols -/

reserve notation `(` a `|` b `)`
reserve infixl `++`:65
reserve infixr `::`:65

-- Yet another trick to anotate an expression with a type
definition is_typeof (A : Type) (a : A) : A := a

notation `typeof` t `:` T  := is_typeof T t
