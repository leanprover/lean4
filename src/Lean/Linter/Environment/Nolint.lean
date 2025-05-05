/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
prelude

/-- `@[nolint linterName]` omits the tagged declaration from being checked by
the linter with name `linterName`. -/
syntax (name := nolint) "nolint" (ppSpace ident)+ : attr

/-- Defines the user attribute `nolint` for skipping `#lint` -/
initialize nolintAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `nolint
    descr := "Do not report this declaration in any of the tests of `#lint`"
    getParam := fun _ => fun
      | `(attr| nolint $[$ids]*) => ids.mapM fun id => withRef id <| do
        let shortName := id.getId.eraseMacroScopes
        let some (declName, _) := (batteriesLinterExt.getState (← getEnv)).find? shortName
          | throwError "linter '{shortName}' not found"
        Elab.addConstInfo id declName
        pure shortName
      | _ => Elab.throwUnsupportedSyntax
  }

/-- Returns true if `decl` should be checked
using `linter`, i.e., if there is no `nolint` attribute. -/
def shouldBeLinted [Monad m] [MonadEnv m] (linter : Name) (decl : Name) : m Bool :=
  return !((nolintAttr.getParam? (← getEnv) decl).getD #[]).contains linter
