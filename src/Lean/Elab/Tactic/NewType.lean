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
`unsealing_newtype N => tacs` runs `tacs` with the `newtype`-declared type `N` -- together with
its auto-generated constructor and projector -- treated as `[semireducible]` instead of
`[irreducible]`. This is the escape hatch for a `newtype`: within the block, `N`, `N.mk` and its
projector unfold like ordinary definitions, e.g. `N = Nat` can be proved by `rfl`.
-/
syntax (name := unsealingNewtype) "unsealing_newtype " ident " => " tacticSeq : tactic

end Lean.Parser.Tactic

namespace Lean.Elab.Tactic
open Meta

/--
Runs `t` with the declarations `names` treated as `[semireducible]`. The combinator underlying
the `unsealing_newtype` tactic; see its docstring.
-/
def unsealingNewtype [Monad m] [MonadEnv m] [MonadFinally m] (names : Array Name) (t : m α) :
    m α := do
  modifyEnv reducibilityExtraExt.pushScope
  for n in names do
    setLocalReducibilityStatus n .semireducible
  try
    t
  finally
    modifyEnv reducibilityExtraExt.popScope

@[builtin_tactic Lean.Parser.Tactic.unsealingNewtype] def evalUnsealingNewtype : Tactic :=
  fun stx => do
    let typeStx := stx[1]
    let typeName ← resolveGlobalConstNoOverload typeStx
    let some info ← getVirtualStructureInfo? typeName
      | throwErrorAt typeStx "'{typeName}' is not a `newtype`-declared type"
    addConstInfo typeStx typeName
    unsealingNewtype #[info.typeName, info.ctorName, info.projName] (evalTactic stx[3])

end Lean.Elab.Tactic
