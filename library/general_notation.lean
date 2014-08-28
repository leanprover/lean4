-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad

-- general_notation
-- ================

-- General operations
-- ------------------

notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r


-- Global declarations of right binding strength
-- ---------------------------------------------

-- If a module reassigns these, it will be incompatible with other modules that adhere to these
-- conventions.

-- ### Logical operations and relations

precedence `¬`:40
precedence `/\`:35    -- infixr
precedence `∧`:35     -- infixr
precedence `\/`:30    -- infixr
precedence `∨`:30     -- infixr
precedence `<->`:25
precedence `↔`:25

precedence `=`:50
precedence `≠`:50
precedence `rfl`:max   -- shorthand for reflexivity

precedence `≈`:50      -- used for path in hott
precedence `∼`:50

precedence `⁻¹`:100
precedence `⬝`:75      -- infixr
precedence `▸`:75      -- infixr

-- ### types and type constructors

precedence `ℕ`:max
precedence `ℤ`:max

precedence `⊎`:25      -- infixr
precedence `×`:30      -- infixr

-- ### arithmetic operations

precedence `+`:65      -- infixl
precedence `-`:65      -- infixl; for negation, follow by rbp 100
precedence `*`:70      -- infixl
precedence `div`:70    -- infixl
precedence `mod`:70    -- infixl

precedence `<=`:50
precedence `≤`:50
precedence `<`:50
precedence `>=`:50
precedence `≥`:50
precedence `>`:50

-- ### boolean operations

precedence `&&`:70     -- infixl
precedence `||`:65     -- infixl
precedence `!`:85      -- boolean negation, follow by rbp 100

-- ### set operations

precedence `∈`:50
precedence `∅`:max
precedence `∩`:70
precedence `∪`:65

-- ### other symbols

precedence `|`:55     -- used for absolute value, subtypes, divisibility
precedence `++`:65    -- list append
precedence `::`:65    -- list cons
