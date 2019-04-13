import parser
open Parser
local infix ` ; `:10 := Parser.andthen
local infix ` || `:5 := Parser.orelse

def mkNumPairKind : IO SyntaxNodeKind := nextKind `numPair
@[init mkNumPairKind] constant numPairKind : SyntaxNodeKind := default _

def mkNumSetKind : IO SyntaxNodeKind := nextKind `numSet
@[init mkNumSetKind] constant numSetKind : SyntaxNodeKind := default _

@[inline2]
def numPair : BasicParser :=
node numPairKind $
  "("; number; ","; number; ")"

@[inline2]
def numSet : BasicParser :=
node numSetKind $
  "{"; sepBy number ","; "}"

def testParser : BasicParser :=
many (numPair || numSet)

@[noinline] def test (p : BasicParser) (s : String) : IO Unit :=
match p.run s with
| Except.error msg := IO.println msg
| Except.ok stx    := IO.println stx

def mkNumPairString : Nat → String → String
| 0     s := s
| (n+1) s := mkNumPairString n $
  s ++ "{} /- /- comment2 -/ -/ "
  ++ "{" ++ toString n ++ "," ++ toString (n+1) ++ ",   " ++ toString (n+2) ++ "}"
  ++ "(" ++ toString n ++ ", " ++ toString n ++ ") -- comment\n"

def main (xs : List String) : IO Unit :=
let s := mkNumPairString xs.head.toNat "" in
test testParser s
