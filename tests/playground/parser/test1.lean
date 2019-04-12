import parser
open Parser
local infix ` ; `:10 := Parser.andthen
local infix ` || `:5 := Parser.orelse

def mkTestKind : IO SyntaxNodeKind := nextKind `test
@[init mkTestKind] constant testKind : SyntaxNodeKind := default _

@[inline2]
def numPair : BasicParser :=
node testKind $
  symbol "("; number; symbol ","; number; symbol ")"

def numPairs : BasicParser :=
many numPair

@[noinline] def test (p : BasicParser) (s : String) : IO Unit :=
match p.run s with
| Except.error msg := IO.println msg
| Except.ok stx    := IO.println stx

def mkNumPairString : Nat → String → String
| 0     s := s
| (n+1) s := mkNumPairString n (s ++ "(" ++ toString n ++ ", " ++ toString n ++ ") -- comment\n")

def main (xs : List String) : IO Unit :=
let s := mkNumPairString xs.head.toNat "" in
test numPairs s
