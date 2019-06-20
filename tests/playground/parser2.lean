import init.lean.name init.lean.syntax init.lean.parser

namespace Lean
namespace Parser

inductive ParserDescr (k : ParserKind := leading)
| ident {}  : ParserDescr
| numLit {} : ParserDescr
| strLit {} : ParserDescr
| symbol {} (sym : String) (lbp : Option Nat) : ParserDescr
| unicodeSymbol {} (sym ascii : String) (lbp : Option Nat) : ParserDescr
| andthen (p q : ParserDescr) : ParserDescr
| orelse (p q : ParserDescr) : ParserDescr
| sepBy (p q : ParserDescr) : ParserDescr
| sepBy1 (p q : ParserDescr) : ParserDescr
| many (p : ParserDescr) : ParserDescr
| many1 (p : ParserDescr) : ParserDescr
| optional (p : ParserDescr) : ParserDescr
| nonTerminal (id : Name) : ParserDescr
| external (fn : Name) : ParserDescr
| node (kind : SyntaxNodeKind) (a : ParserDescr) : ParserDescr

abbrev TrailingParserDescr := ParserDescr trailing

def toParser {k : ParserKind} : ParserDescr k → ExceptT String Id (Parser k)
| ParserDescr.ident            := pure ident
| ParserDescr.numLit           := pure numLit
| ParserDescr.strLit           := pure strLit
| (ParserDescr.andthen p q)    := do p ← toParser p, q ← toParser q, pure (andthen p q)
| (ParserDescr.orelse p q)     := do p ← toParser p, q ← toParser q, pure (orelse p q)
| (ParserDescr.symbol sym lbp) := pure (symbol sym lbp)
| _ := Except.error "not implemented yet"

end Parser
end Lean
