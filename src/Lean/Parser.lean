/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Basic
import Lean.Parser.Level
import Lean.Parser.Term
import Lean.Parser.Tactic
import Lean.Parser.Command
import Lean.Parser.Module
import Lean.Parser.Syntax
import Lean.Parser.Do

namespace Lean
namespace Parser

builtin_initialize
  registerAlias "ws" checkWsBefore
  registerAlias "noWs" checkNoWsBefore
  registerAlias "num" numLit
  registerAlias "str" strLit
  registerAlias "char" charLit
  registerAlias "name" nameLit
  registerAlias "ident" ident
  registerAlias "colGt" checkColGt
  registerAlias "colGe" checkColGe
  registerAlias "lookahead" lookahead
  registerAlias "atomic" atomic
  registerAlias "many" many
  registerAlias "many1" many1
  registerAlias "notFollowedBy" (notFollowedBy · "element")
  registerAlias "optional" optional
  registerAlias "withPosition" withPosition
  registerAlias "interpolatedStr" interpolatedStr
  registerAlias "sepBy" sepBy
  registerAlias "sepBy1" sepBy1
  registerAlias "orelse" orelse
  registerAlias "andthen" andthen
  registerAlias "sepByT" (sepBy (allowTrailingSep := true))
  registerAlias "sepBy1T" (sepBy1 (allowTrailingSep := true))

end Parser

namespace PrettyPrinter
namespace Parenthesizer

-- Close the mutual recursion loop; see corresponding `[extern]` in the parenthesizer.
@[export lean_mk_antiquot_parenthesizer]
def mkAntiquot.parenthesizer (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Parenthesizer :=
  Parser.mkAntiquot.parenthesizer name kind anonymous

-- The parenthesizer auto-generated these instances correctly, but tagged them with the wrong kind, since the actual kind
-- (e.g. `ident`) is not equal to the parser name `Lean.Parser.Term.ident`.
@[builtinParenthesizer ident] def ident.parenthesizer : Parenthesizer := Parser.Term.ident.parenthesizer
@[builtinParenthesizer numLit] def numLit.parenthesizer : Parenthesizer := Parser.Term.num.parenthesizer
@[builtinParenthesizer scientificLit] def scientificLit.parenthesizer : Parenthesizer := Parser.Term.scientific.parenthesizer
@[builtinParenthesizer charLit] def charLit.parenthesizer : Parenthesizer := Parser.Term.char.parenthesizer
@[builtinParenthesizer strLit] def strLit.parenthesizer : Parenthesizer := Parser.Term.str.parenthesizer

end Parenthesizer

namespace Formatter

@[export lean_mk_antiquot_formatter]
def mkAntiquot.formatter (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Formatter :=
  Parser.mkAntiquot.formatter name kind anonymous

@[builtinFormatter ident] def ident.formatter : Formatter := Parser.Term.ident.formatter
@[builtinFormatter numLit] def numLit.formatter : Formatter := Parser.Term.num.formatter
@[builtinFormatter scientificLit] def scientificLit.formatter : Formatter := Parser.Term.scientific.formatter
@[builtinFormatter charLit] def charLit.formatter : Formatter := Parser.Term.char.formatter
@[builtinFormatter strLit] def strLit.formatter : Formatter := Parser.Term.str.formatter

end Formatter
end PrettyPrinter
end Lean
