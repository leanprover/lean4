/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.VirtualStructure

public section

namespace Lean.Parser.Tactic

/--
`with_reducible_type N => tacs` runs `tacs` with the `type_def`-declared type `N` -- together with
its auto-generated constructor and projector -- temporarily relaxed from `[irreducible]` to
`[reducible]`, restoring the original status afterward even if `tacs` fails. This is the escape
hatch for a `type_def` type: within the block, `N`, `N.mk` and its projector unfold like ordinary
reducible definitions, enabling the `rfl`-style defeq abuse that is disallowed everywhere else.
-/
syntax (name := withReducibleType) "with_reducible_type " ident " => " tacticSeq : tactic

end Lean.Parser.Tactic

namespace Lean.Elab.Tactic

/-- Combinator underlying the `with_reducible_type` tactic; see its docstring. -/
def withReducibleType [Monad m] [MonadEnv m] [MonadFinally m] [MonadResolveName m]
    [MonadOptions m] [MonadLog m] [AddMessageContext m] [MonadError m]
    (typeStx : Syntax) (t : m α) : m α := do
  let typeName ← resolveGlobalConstNoOverload typeStx
  let some info ← getVirtualStructureInfo? typeName
    | throwErrorAt typeStx "'{typeName}' is not a `type_def`-declared type"
  let names := #[info.typeName, info.ctorName, info.projName]
  let origStatuses ← names.mapM getReducibilityStatus
  for n in names do
    setReducibilityStatus n .reducible
  try
    t
  finally
    for (n, s) in names.zip origStatuses do
      setReducibilityStatus n s

@[builtin_tactic Lean.Parser.Tactic.withReducibleType] def evalWithReducibleType : Tactic :=
  fun stx => withReducibleType stx[1] (evalTactic stx[3])

end Lean.Elab.Tactic
