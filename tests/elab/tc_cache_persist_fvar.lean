import Lean

/-!
Tests that free-variable-dependent type class resolution cache entries are not persisted across
commands.

A `FVarId` identifies a variable only within the `NameGenerator` that created it. The pretty
printer runs with a fresh one (`PPContext.runCoreM`), so a delaborator that synthesizes an instance
under a binder sees the same `FVarId`s in every command. Persisting an entry keyed by such a
variable makes the next command's unrelated query hit it. Reduced from Mathlib's `max`/`⊔`
delaborator, which decides on notation by testing for a `LinearOrder` instance.
-/

open Lean

class Foo (α : Type) where
class Bar (α : Type) where

def wrap {α : Type} (a : α) : α := a

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.wrap]
def delabWrap : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 2)
  let α := e.appFn!.appArg!
  -- The pretty printer clears the local instances, so re-add them, as Mathlib's delaborator does.
  let decls := (← getLCtx).decls.toList.filterMap id
  let r? ← withLocalInstances decls do
    synthInstance? (mkApp (mkConst ``Foo) α)
  let a ← withAppArg delab
  let tag := mkIdent (if r?.isSome then `FOO else `NOFOO)
  `($tag $a)

-- Delaborating this fails to synthesize `Foo _pp_uniq.1`.
/-- info: fun α [Bar α] a => NOFOO a : (α : Type) → [Bar α] → α → α -/
#guard_msgs in
#check fun (α : Type) [Bar α] (a : α) => wrap a

-- The binder is a different variable that merely reuses the `FVarId`, and `Foo` is synthesizable
-- from it, so the failure above must not be reused.
/-- info: fun α [Foo α] a => FOO a : (α : Type) → [Foo α] → α → α -/
#guard_msgs in
#check fun (α : Type) [Foo α] (a : α) => wrap a
