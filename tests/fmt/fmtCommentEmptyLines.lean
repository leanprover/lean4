/-!
Tests that the formatter retains an empty line between two adjacent comments on lines of their own
when the input has one or more empty lines between them. Several empty lines become one empty line,
and comments with no empty line between them stay together.
-/

def a := 1
def b := 2
def f (x y : Nat) : Nat := x + y

-- One empty line between the comments.
def oneEmptyLine :=
  -- first comment

  -- second comment
  a

-- Several empty lines between the comments become one empty line.
def severalEmptyLines :=
  -- first comment


  -- second comment
  a

-- A line that contains only spaces is an empty line.
def emptyLineWithSpaces :=
  -- first comment
    
  -- second comment
  a

-- Comments with no empty line between them stay together.
def noEmptyLine :=
  -- first comment
  -- second comment
  a

-- Only the empty lines of the input are retained.
def mixedGroups :=
  -- first group, first line
  -- first group, second line

  -- second group

  -- third group, first line
  -- third group, second line
  a

-- Block comments on lines of their own.
def blockComments :=
  /- first comment -/

  /- second comment -/
  a

-- A block comment and a line comment on lines of their own.
def blockAndLineComment :=
  /- block comment -/

  -- line comment

  /-
  multi-line
  block comment
  -/
  a

-- A block comment directly before a line comment does not get an empty line.
def blockBeforeLineComment :=
  /- block comment -/
  -- line comment
  a

-- Comments before an argument.
def beforeArgument :=
  f a
    -- first comment

    -- second comment
    b

-- Comments in a tactic block.
theorem inTacticBlock : True ∧ True := by
  constructor
  -- first comment

  -- second comment
  · trivial
  -- third comment


  -- fourth comment
  · trivial

-- Comments in a `do` block.
def inDoBlock : IO Unit := do
  IO.println "start"
  -- first comment

  -- second comment
  IO.println "end"

-- Comments between structure fields.
structure Point where
  x : Nat
  -- first comment

  -- second comment
  y : Nat

-- Comments between match alternatives.
def describe (n : Nat) : String :=
  match n with
  | 0 => "zero"
  -- first comment

  -- second comment
  | _ => "many"

-- Comments before a closing bracket.
def numbers := [
  a,
  b
  -- first comment

  -- second comment
  ]

-- Comments that cannot be placed directly before their token are inserted after rendering, before
-- the line of the token.
def beforeClosingParen : IO Unit := do
  IO.println "start"
  IO.println (toString a
    -- first comment

    -- second comment
    )

-- Comments after an operator on a line of its own move above the operator, with the empty line.
def afterOperator :=
  a
  + -- first comment

  -- second comment
  b

-- The empty line between a comment at the end of a line and the next comment is not retained.
def afterEndOfLineComment :=
  f a -- end-of-line comment

  -- next comment
  b
