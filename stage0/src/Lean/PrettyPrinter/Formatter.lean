/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

import Lean.Parser
import Lean.Elab.Quotation

namespace Lean
namespace PrettyPrinter
namespace Formatter

structure Context :=
(table : Parser.TokenTable)

structure State :=
(stxTrav : Syntax.Traverser)
(leadWord : String := "")

end Formatter

abbrev FormatterM := ReaderT Formatter.Context $ StateT Formatter.State MetaM

abbrev Formatter := Expr → FormatterM Format

unsafe def mkFormatterAttribute : IO (KeyedDeclsAttribute Formatter) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinFormatter,
  name := `formatter,
  descr := "Register a formatter.

[formatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.",
  valueTypeName := `Lean.PrettyPrinter.Formatter,
  evalKey := fun env args => match attrParamSyntaxToIdentifier args with
    | some id => match env.find? id with
      | some _ => pure id
      | none   => throw ("invalid [formatter] argument, unknown identifier '" ++ toString id ++ "'")
    | none    => throw "invalid [formatter] argument, expected identifier"
} `Lean.PrettyPrinter.formatterAttribute
@[init mkFormatterAttribute] constant formatterAttribute : KeyedDeclsAttribute Formatter := arbitrary _

end PrettyPrinter
end Lean
