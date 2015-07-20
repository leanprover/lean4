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
reserve infixr `∧`:35
reserve infixr `/\`:35
reserve infixr `\/`:30
reserve infixr `∨`:30
reserve infix `<->`:20
reserve infix `↔`:20
reserve infix `=`:50
reserve infix `≠`:50
reserve infix `≈`:50
reserve infix `~`:50
reserve infix `≡`:50

reserve infixr `∘`:60                   -- input with \comp
reserve postfix `⁻¹`:std.prec.max_plus  -- input with \sy or \-1 or \inv

reserve infixl `⬝`:75
reserve infixr `▸`:75
reserve infixr `▹`:75

/- types and type constructors -/

reserve infixl `⊎`:25
reserve infixl `×`:30

/- arithmetic operations -/

reserve infixl `+`:65
reserve infixl `-`:65
reserve infixl `*`:70
reserve infixl `div`:70
reserve infixl `mod`:70
reserve infixl `/`:70
reserve prefix `-`:100
reserve infix `^`:80

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
reserve infix `⊆`:50

/- other symbols -/

reserve infix `∣`:50
reserve infixl `++`:65
reserve infixr `::`:65
