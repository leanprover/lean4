/-!
Tests that the fallback comment insertion mechanism, which inserts comments into the rendered
output rather than into the document, does not place a comment within the rendering of syntax
without a formatter that spans several lines. Such syntax keeps its tokens, its comments and its
layout, so a comment between its lines can end up in a token or in a comment of that syntax, and
formatting the output again reads the comment as a part of that syntax.
-/

syntax:max "both " term:max term:max : term

macro_rules
  | `(both $a $b) => `($a + $b)

syntax:max "join " term:max term:max : term

macro_rules
  | `(join $a $b) => `($a ++ $b)

notation:65 a " +++ " b => a ++ b ++ ""

def f (a b : String) : String := a ++ b

/-! A comment on its own line before the closing bracket, after syntax without a formatter. -/

def beforeClosingBracket : String :=
  (/- first -/
  "a"
      +++ "b"
    /- second -/
    )

-- The same with comments that do not fit on a line of their own.
def longBeforeClosingBracket : String :=
  (/- first xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx -/
  "a"
      +++ "b"
    /- second xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx -/
    )

-- The same for a syntax quotation, which keeps its layout too.
def quotation : Lean.MacroM Lean.Syntax :=
  (/- first -/
  `(1
      + 2)
    -- second
    )

/-!
A token that spans several lines in syntax without a formatter. The comment after the syntax is
placed before the line of the next token, which starts within that token.
-/

def afterMultiLineString : String := f (join "first xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
  more" "c") /- second
  more -/ "d"

def afterMultiLineIdent («first xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
  more» : String) : String := f (join «first xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
  more» "c") /- second
  more -/ "d"

/-!
A comment that spans several lines in syntax without a formatter. The second comment is placed
before the line of its token, which starts within the first comment.
-/

def inTypeAscription : Nat := (both 1 /- first xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
  more -/ 2 : /- second
  more -/ Nat)

def inArgument (g : Nat → Nat → Nat) : Nat := g (both 1 /- first xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
  more -/ 2) /- second
  more -/ 3

-- A comment within a comment.
def nestedComment : Nat := (both 1 /- first /- nested
  more -/ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
  more -/ 2 : /- second
  more -/ Nat)

-- A line comment with the start of a block comment.
def lineComment : Nat := (both 1 -- first /- xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
  2 : /- second
  more -/ Nat)

-- A comment on one line.
def onOneLine : Nat := (both 1 /- first -/
  2 : /- second
  more -/ Nat)

/-! A comment before syntax without a formatter that has a line comment on its first line. -/

def beforeLineComment : String := (-- first
  join "a" -- second
    "b")
