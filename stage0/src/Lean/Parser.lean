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
namespace PrettyPrinter
namespace Parenthesizer

-- Close the mutual recursion loop; see corresponding `[extern]` in the parenthesizer.
@[export lean_mk_antiquot_parenthesizer]
def mkAntiquot.parenthesizer (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Parenthesizer :=
Parser.mkAntiquot.parenthesizer name kind anonymous

-- The parenthesizer auto-generated these instances correctly, but tagged them with the wrong kind, since the actual kind
-- (e.g. `ident`) is not equal to the parser name `Lean.Parser.Term.ident`.
@[builtinParenthesizer ident] def ident.parenthesizer := Parser.Term.ident.parenthesizer
@[builtinParenthesizer numLit] def numLit.parenthesizer := Parser.Term.num.parenthesizer
@[builtinParenthesizer charLit] def charLit.parenthesizer := Parser.Term.char.parenthesizer
@[builtinParenthesizer strLit] def strLit.parenthesizer := Parser.Term.str.parenthesizer

end Parenthesizer

namespace Formatter

@[export lean_mk_antiquot_formatter]
def mkAntiquot.formatter (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Formatter :=
Parser.mkAntiquot.formatter name kind anonymous

@[builtinFormatter ident] def ident.formatter := Parser.Term.ident.formatter
@[builtinFormatter numLit] def numLit.formatter := Parser.Term.num.formatter
@[builtinFormatter charLit] def charLit.formatter := Parser.Term.char.formatter
@[builtinFormatter strLit] def strLit.formatter := Parser.Term.str.formatter

end Formatter
end PrettyPrinter
end Lean
