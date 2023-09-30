/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.ElabRules
import Lake.DSL.Extensions

namespace Lake.DSL
open Lean Elab Term

/--
A dummy default constant for `__dir__` to make it type check
outside Lakefile elaboration (e.g., when editing).
-/
opaque dummyDir : System.FilePath

/--
A dummy default constant for `get_config` to make it type check
outside Lakefile elaboration (e.g., when editing).
-/
opaque dummyGetConfig? : Name → Option String

/--
A macro that expands to the path of package's directory
during the Lakefile's elaboration.
-/
scoped syntax (name := dirConst) "__dir__" : term

@[term_elab dirConst]
def elabDirConst : TermElab := fun stx expectedType? => do
  let exp :=
    if let some dir := dirExt.getState (← getEnv) then
      let str := Syntax.mkStrLit dir.toString (SourceInfo.fromRef stx)
      Syntax.mkApp (mkCIdentFrom stx ``System.FilePath.mk) #[str]
    else
      -- `id` app forces Lean to show macro's doc rather than the constant's
      Syntax.mkApp (mkCIdentFrom stx ``id) #[mkCIdentFrom stx ``dummyDir]
  withMacroExpansion stx exp <| elabTerm exp expectedType?

/--
A macro that expands to the specified configuration option (or `none`,
if the option has not been set) during the Lakefile's elaboration.

Configuration arguments are set either via the Lake CLI (by the `-K` option)
or via the `with` clause in a `require` statement.
-/
scoped syntax (name := getConfig) "get_config? " ident :term

@[term_elab getConfig]
def elabGetConfig : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(getConfig| get_config? $key) => do
    let exp : Term ← show TermElabM Term from do
      if let some opts := optsExt.getState (← getEnv) then
        if let some val := opts.find? key.getId then
          `(some $(Syntax.mkStrLit val <| SourceInfo.fromRef (← getRef)))
        else
          -- Make sure `none` is properly typed
          `((none : Option String))
      else
        return Syntax.mkApp (mkCIdentFrom stx ``dummyGetConfig?) #[quote key.getId]
    withMacroExpansion stx exp <| elabTerm exp expectedType?
  | _ => throwUnsupportedSyntax
