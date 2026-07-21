module

/-!
Tests for the `linter.checkUnivs` linter, which warns when a declaration has a universe
parameter that only ever occurs in a `max u v` together with another parameter, never
on its own.
-/

set_option linter.checkUnivs true

universe u v w

-- Good: each universe parameter occurs alone somewhere.
def goodUnivs (α : Type u) (β : Type v) : Type (max u v) := α × β

-- Good: `u` occurs alone in `α`, so the `max u v` is fine.
def goodUnivsDominated (α : Type u) (β : Type (max u v)) : Type (max u v) := α × β

-- Bad: neither `u` nor `v` occur alone in `badUnivs`'s type.
/--
warning: `badUnivs`: universes `u`, `v` only occur together. This usually means there is a `max` expression in the type where none of these universes appear on their own.

Note: This linter can be disabled with `set_option linter.checkUnivs false`
-/
#guard_msgs in
def badUnivs (α : Type (max u v)) : Type (max u v) := α

-- `set_option ... false in` suppresses the warning locally.
#guard_msgs in
set_option linter.checkUnivs false in
def badUnivsSuppressed (α : Type (max u v)) : Type (max u v) := α

-- Inductives are also checked.
/--
warning: `BadInd`: universes `u`, `v` only occur together. This usually means there is a `max` expression in the type where none of these universes appear on their own.

Note: This linter can be disabled with `set_option linter.checkUnivs false`
-/
#guard_msgs in
inductive BadInd : Type (max u v) where
  | mk

-- Good: a structure whose universes each occur alone in a field. The `max` in the structure's
-- own type is forced, so this must not warn even though the type looks like `badUnivs`.
-- See https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/checkUnivs.20linter.20for.20structure
#guard_msgs in
structure Signature where
  constants : Type u
  vars : Type v
  relationSymbols : Type w
  relationArity : relationSymbols → Nat

-- Bad: the only field glues `u` and `v`, so neither occurs alone in any constructor field either.
/--
warning: `BadStruct.a`: universes `u`, `v` only occur together. This usually means there is a `max` expression in the type where none of these universes appear on their own.

Note: This linter can be disabled with `set_option linter.checkUnivs false`
---
warning: `BadStruct`: universes `u`, `v` only occur together. This usually means there is a `max` expression in the type where none of these universes appear on their own.

Note: This linter can be disabled with `set_option linter.checkUnivs false`
-/
#guard_msgs in
structure BadStruct where
  a : Type (max u v)
