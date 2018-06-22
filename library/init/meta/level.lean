/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.name init.lean.level

export lean (level level.zero level.succ level.max level.imax level.param level.of_nat level.has_param)

/- TODO(Leo): provide a definition in Lean. -/
meta constant level.has_decidable_eq : decidable_eq level
attribute [instance] level.has_decidable_eq
meta constant level.lt : level → level → bool
meta constant level.lex_lt : level → level → bool
meta constant level.fold {α :Type} : level → α → (level → α → α) → α
/-- Return the given level expression normal form -/
meta constant level.normalize : level → level
/-- Return tt iff lhs and rhs denote the same level.
   The check is done by normalization. -/
meta constant level.eqv : level → level → bool
/-- Return tt iff the first level occurs in the second -/
meta constant level.occurs : level → level → bool
/-- Replace a parameter named n with l in the first level if the list contains the pair (n, l) -/
meta constant level.instantiate : level → list (name × level) → list level
