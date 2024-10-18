/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Lean.Elab.InfoTree.Main
import Lean.DocString.Extension

namespace Lean

builtin_initialize
  registerBuiltinAttribute {
    name := `inherit_doc
    descr := "inherit documentation from a specified declaration"
    add   := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwError "invalid `[inherit_doc]` attribute, must be global"
      match stx with
      | `(attr| inherit_doc $[$id?:ident]?) => withRef stx[0] do
        let some id := id?
          | throwError "invalid `[inherit_doc]` attribute, could not infer doc source"
        let declName ← Elab.realizeGlobalConstNoOverloadWithInfo id
        if (← findSimpleDocString? (← getEnv) decl (includeBuiltin := false)).isSome then
          logWarning m!"{← mkConstWithLevelParams decl} already has a doc string"
        let some doc ← findSimpleDocString? (← getEnv) declName
          | logWarningAt id m!"{← mkConstWithLevelParams declName} does not have a doc string"
        addDocString decl doc
      | _  => throwError "invalid `[inherit_doc]` attribute"
  }
