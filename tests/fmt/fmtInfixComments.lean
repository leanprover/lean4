/-!
Tests the placement of comments around the operators of infix operations.
A comment following an operator is attached to the operator by `collectComments`, which drags it
along when the operation is laid out differently; `Lean.Fmt.infixOperatorCommentCollector` attaches
it to the operand it shares its line with instead, or moves it above an operator that has a line of
its own.
-/

def a := 1
def b := 2
def c := 3
def aVeryLongOperandName := 4
def anotherVeryLongOperandName := 5

-- The operator trails its left operand's line, so the comment belongs to that operand.
def trailingOperator :=
  a + -- the left operand
  b

-- The same for a block comment.
def blockAfterTrailingOperator :=
  a + /- the left operand -/
  b

-- The operator leads its right operand's line, so the comment belongs to that operand.
def leadingOperator :=
  a
  + /- the right operand -/ b

-- The operator has a line of its own, so the comment moves above it.
def separateOperator :=
  a
  + -- the operator
  b

-- A comment that is already above the operator stays there, so the two forms agree.
def commentAboveOperator :=
  a
  -- the operator
  + b

-- Comments attached to the operands themselves are left alone.
def commentsOnOperands :=
  a -- the left operand
  + b -- the right operand

-- A comment before the whole operation stays before it.
def commentBeforeOperation :=
  -- the operation
  a + b

-- The whole operation is on one line, so there is no other line to move the comment to.
def singleLineOperation := a + /- in the middle -/ b

-- In a chain, the comment stays with the operand next to the operator it follows.
def chain :=
  a + b * c + -- the third operand
  a + b

-- The same for an operator leading a line within a chain.
def chainWithLeadingOperator :=
  a + b
  + /- the fourth operand -/ c * a

-- A comment on its own line between the operator and its right operand shares its line with
-- neither operand, so it moves above the operator.
def commentBeforeRightOperand :=
  a +
  -- the right operand
  b

-- Comparison and logical operators behave the same way.
def comparison :=
  aVeryLongOperandName == -- the left operand
  anotherVeryLongOperandName

def conjunction :=
  aVeryLongOperandName > 0
  && -- the operator
  anotherVeryLongOperandName > 0

-- Operands that are long enough to force the operation apart.
def longOperands :=
  aVeryLongOperandName + anotherVeryLongOperandName + -- the second operand
  aVeryLongOperandName + anotherVeryLongOperandName + aVeryLongOperandName

-- Several comments after operators of the same chain.
def severalComments :=
  a + -- the first operand
  b + -- the second operand
  c

-- Each comment of a run after the operator is placed on its own.
def commentGroup :=
  a + -- the first line
  -- the second line
  b

-- Arrows behave the same way, including chains that mix the plain and the dependent arrow.
def arrow : Type :=
  Nat → -- the left operand
  Nat

def dependentArrowChain : Type :=
  (n : Nat) → Nat → -- the second operand
  Nat

def arrowOnItsOwnLine : Type :=
  Nat
  → -- the operator
  Nat

-- Operations nested in an application.
def nestedInApplication :=
  max (a + -- the left operand
    b) (a
    + /- the right operand -/ b)
