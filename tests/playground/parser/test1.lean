import parser
open Parser

def mkNumPairKind : IO SyntaxNodeKind := nextKind `numPair
@[init mkNumPairKind] constant numPairKind : SyntaxNodeKind := default _

def mkNumSetKind : IO SyntaxNodeKind := nextKind `numSet
@[init mkNumSetKind] constant numSetKind : SyntaxNodeKind := default _

def mkParenIdentKind : IO SyntaxNodeKind := nextKind `parenIdent
@[init mkParenIdentKind] constant parenIdentKind : SyntaxNodeKind := default _

def mkQualifiedKind : IO SyntaxNodeKind := nextKind `qualified
@[init mkQualifiedKind] constant qualifiedKind : SyntaxNodeKind := default _

def mkSeqKind : IO SyntaxNodeKind := nextKind `seq
@[init mkSeqKind] constant seqKind : SyntaxNodeKind := default _

def mkSetCompKind : IO SyntaxNodeKind := nextKind `setComp
@[init mkSetCompKind] constant setCompKind : SyntaxNodeKind := default _

-- set_option pp.implicit true
-- set_option trace.compiler.boxed true
-- set_option trace.compiler.lambda_pure true

def numPairP : TermParser :=
node numPairKind $
  "("; number; ","; number; ")"

def numSetP : TermParser :=
node numSetKind $
  "{"; sepBy number ","; "}"

def testParser1 : TermParser :=
many (numPairP <|> numSetP)

def parenIdentP : TermParser :=
node parenIdentKind $
  "("; ident; ")"

def qualifiedP : TermParser :=
node qualifiedKind $
  "("; ident; ":"; ident; ")"

def seqP : TermParser :=
node seqKind $
  "("; sepBy ident ":"; ")"

def setCompP : TermParser :=
node setCompKind $
  "{"; ident; ":"; ident; "|"; ident; "}"

def testParser2 : TermParser :=
many (longestMatch [qualifiedP, parenIdentP, seqP, setCompP])

def testParser3 : TermParser :=
many (longestMatch [qualifiedP, seqP])

@[noinline] def test (p : TermParser) (s : String) : IO Unit :=
match p.test s with
| Except.error msg := IO.println msg
| Except.ok stx    := IO.println "ok" -- IO.println stx -- IO.println "ok"

def mkTestString1 : Nat → String → String
| 0     s := s
| (n+1) s := mkTestString1 n $
  s ++ "{} /- /- comment2 -/ -/ "
  ++ "{" ++ toString n ++ "," ++ toString (n+1) ++ ",   " ++ toString (n+2) ++ "}"
  ++ "(" ++ toString n ++ ", " ++ toString n ++ ") -- comment\n"

def test1 (n : Nat) : IO Unit :=
let s := mkTestString1 n "" in
test testParser1 s

def mkTestString2 : Nat → String → String
| 0     s := s
| (n+1) s := mkTestString2 n $
  s ++ "(xyz) /- /- comment2 -/ -/ "
  ++ "(x:y:z) -- comment1 \n"
  ++ "(x:y)"

def test2 (n : Nat) : IO Unit :=
let s := mkTestString2 n "" in
test testParser2 s

def test3 (n : Nat) : IO Unit :=
let s := mkTestString2 n "" in
test testParser3 s

def main (xs : List String) : IO Unit :=
timeit "test2" (test2 xs.head.toNat) *>
timeit "test3" (test3 xs.head.toNat)
