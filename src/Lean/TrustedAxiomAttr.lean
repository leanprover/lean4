/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Attributes
import Lean.Util.CollectAxioms
import Lean.Util.Sorry
import Lean.Linter.Init
import Lean.AddDecl

namespace Lean

/--
Marks an axiom as "trusted" so that the `linter.untrustedAxioms` linter does not warn about
declarations depending on axioms tagged with this attribute.
-/
@[builtin_doc]
public builtin_initialize trustedAxiomAttr : TagAttribute ←
  registerTagAttribute `trusted_axiom "mark an axiom as trusted so that `linter.untrustedAxioms` does not warn about declarations depending on it" fun declName => do
    unless getOriginalConstKind? (← getEnv) declName matches some .axiom do
      throwError "Cannot add attribute `@[trusted_axiom]` to non-axiom `{.ofConstName declName}`"

public register_builtin_option linter.untrustedAxioms : Bool := {
  defValue := false
  descr    := "Warn when a declaration added to the environment depends on an axiom that is not \
    tagged with `@[trusted_axiom]`. This should be considered a preliminary elaboration-side \
    check that does not replace the use of external checker tools such as `comparator` with \
    their own axiom checks."
}

open Linter in
public def warnIfUsesUntrustedAxioms (declName : Name) : CoreM Unit := do
  unless getLinterValue linter.untrustedAxioms (← getLinterOptions) do return
  if (← MonadLog.hasErrors) then return
  let env ← getEnv
  let some info := env.find? declName | return
  if info.isUnsafe then return
  if warn.sorry.get (← getOptions) &&
      (info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry)) then
    return
  let axioms ← collectAxioms declName
  let offending := axioms.filter (!trustedAxiomAttr.hasTag env ·)
  unless offending.isEmpty do
    let axMsgs := offending.toList.map fun ax => m!"`{MessageData.ofConstName ax}`"
    logLint linter.untrustedAxioms (← getRef)
      m!"declaration depends on axioms that are not tagged \
        `@[trusted_axiom]`: {MessageData.joinSep axMsgs ", "}"

end Lean
