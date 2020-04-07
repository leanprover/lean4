/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

prelude
import Init.Lean.Parser
import Init.Lean.Elab.Command
import Init.Lean.Delaborator

namespace Lean

namespace PrettyPrinter

constant Parenthesizer : Type := Unit  -- TODO

unsafe def mkParenthesizerAttribute : IO (KeyedDeclsAttribute Parenthesizer) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinParenthesizer,
  name := `parenthesizer,
  descr := "Register a parenthesizer.

[parenthesizer kind] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind`
`kind`.",
  valueTypeName := `Lean.PrettyPrinter.Parenthesizer,
  evalKey := fun env args => match attrParamSyntaxToIdentifier args with
    | some id => match env.find? id with
      | some _ => pure id
      | none   => throw ("invalid [parenthesizer] argument, unknown identifier '" ++ toString id ++ "'")
    | none    => throw "invalid [parenthesizer] argument, expected identifier"
} `Lean.PrettyPrinter.parenthesizerAttribute
@[init mkParenthesizerAttribute] constant parenthesizerAttribute : KeyedDeclsAttribute Parenthesizer := arbitrary _

end PrettyPrinter

end Lean
