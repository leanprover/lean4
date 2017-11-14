/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.name init.meta.format

/-- Reflect a C++ level object. The VM replaces it with the C++ implementation. -/
meta inductive level
| zero   : level
| succ   : level → level
| max    : level → level → level
| imax   : level → level → level
| param  : name → level
| mvar   : name → level

meta instance : inhabited level :=
⟨level.zero⟩

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
meta constant level.to_format : level → options → format
meta constant level.to_string : level → string

meta instance : has_to_string level :=
⟨level.to_string⟩

meta instance : has_to_format level :=
⟨λ l, level.to_format l options.mk⟩

meta def level.of_nat : nat → level
| 0            := level.zero
| (nat.succ n) := level.succ (level.of_nat n)

meta def level.has_param : level → name → bool
| (level.succ l)     n  := level.has_param l n
| (level.max l₁ l₂)  n  := level.has_param l₁ n || level.has_param l₂ n
| (level.imax l₁ l₂) n  := level.has_param l₁ n || level.has_param l₂ n
| (level.param n₁)   n  := n₁ = n
| l                  n  := ff
