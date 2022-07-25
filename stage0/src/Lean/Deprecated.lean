/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Log
import Lean.Attributes

namespace Lean

builtin_initialize deprecatedAttr : ParametricAttribute (Option Name) ←
  registerParametricAttribute {
    name := `deprecated
    descr := "mark declaration as deprecated",
    getParam := fun _ stx => do
     match stx with
     | `(attr| deprecated $[$id?]?) =>
       let some id := id? | return none
       let declNameNew ← resolveGlobalConstNoOverload id
       return some declNameNew
     | _  => throwError "invalid `[deprecated]` attribute"
  }

def isDeprecated (env : Environment) (declName : Name) : Bool :=
  Option.isSome <| deprecatedAttr.getParam? env declName

def getDeprecatedNewName (env : Environment) (declName : Name) : Option Name :=
  match deprecatedAttr.getParam? env declName with
  | some newName? => newName?
  | none => none

def checkDeprecated [Monad m] [MonadEnv m] [MonadLog m] [AddMessageContext m] [MonadOptions m] (declName : Name) : m Unit := do
  match deprecatedAttr.getParam? (← getEnv) declName with
  | none => pure ()
  | some none => logWarning m!"`{declName}` has been deprecated"
  | some (some newName) => logWarning m!"`{declName}` has been deprecated, use `{newName}` instead"

end Lean
