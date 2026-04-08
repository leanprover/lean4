/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

prelude
import Lean.Elab.InfoTree.Main

namespace Lean

/--
Uses documentation from a specified declaration.

`@[inherit_doc decl]` is used to inherit the documentation from the declaration `decl`.
-/
@[builtin_doc]
public builtin_initialize
  registerBuiltinAttribute {
    name := `inherit_doc
    descr := "inherit documentation from a specified declaration"
    add   := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal `inherit_doc kind
      match stx with
      | `(attr| inherit_doc $[$id?:ident]?) => withRef stx[0] do
        let some id := id?
          | throwError "Invalid `[inherit_doc]` attribute: Could not infer doc source"
        -- allow inheriting private docstrings
        let declName ← withoutExporting <| Elab.realizeGlobalConstNoOverloadWithInfo id
        if (← findSimpleDocString? (← getEnv) decl (includeBuiltin := false)).isSome then
          logWarning m!"{← mkConstWithLevelParams decl} already has a doc string"
        -- Outside the server, we do not have access to all docstrings
        if !(← getEnv).header.isModule || Elab.inServer.get (← getOptions) then
          if (← findInternalDocString? (← getEnv) declName).isNone then
            logWarningAt id m!"{← mkConstWithLevelParams declName} does not have a doc string"
        addInheritedDocString decl declName
      | _  => throwError "Invalid `[inherit_doc]` attribute syntax"
    applicationTime := AttributeApplicationTime.afterCompilation
  }
