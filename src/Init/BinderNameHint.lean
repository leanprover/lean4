/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Init.Prelude
import Init.Tactics

set_option linter.unusedVariables false in
/--
The expression `binderNameHint v binder e` defined to be `e`.

If it is used on the right-hand side of an equation that is used for rewriting by `rw` or `simp`,
and `v` is a local variable, and `binder` is an expression that (after beta-reduction) is a binder
(`fun w => …` or `∀ w, …`), then it will rename `v` to the name used in that binder, and remove
the `binderNameHint`.

A typical use of this gadget would be as follows; the gadget ensures that after rewriting, the local
variable is still `name`, and not `x`:
```
theorem all_eq_not_any_not (l : List α) (p : α → Bool) :
    l.all p = !l.any fun x => binderNameHint x p (!p x) := sorry

example (names : List String) : names.all (fun name => "Waldo".isPrefixOf name) = true := by
  rw [all_eq_not_any_not]
  -- ⊢ (!names.any fun name => !"Waldo".isPrefixOf name) = true
```

If `binder` is not a binder, then the name of `v` attains a macro scope. This only matters when the
resulting term is used in a non-hygienic way, e.g. in termination proofs for well-founded recursion.

This gadget is supported by
* `simp`, `dsimp` and `rw` in the right-hand-side of an equation
* `simp` in the assumptions of congruence rules

It is ineffective in other positions (hyptheses of rewrite rules) or when used by other tactics
(e.g. `apply`).
-/
@[simp ↓]
def binderNameHint {α : Sort u} {β : Sort v} {γ : Sort w} (v : α) (binder : β) (e : γ) : γ := e
