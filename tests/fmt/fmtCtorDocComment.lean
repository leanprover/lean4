/-!
Tests that a line comment between the `|` of a constructor and the doc comment of the constructor
is not inserted into the doc comment, where it would become part of the docstring.
-/

inductive LineCommentBeforeDoc where
  | -- c1
    /--
    first line of the doc comment,
    second line
    -/
    a
  | b

-- The text of the doc comment starts on the line of `/--`.
inductive DocStartsOnFirstLine where
  | -- c2
    /-- first line of the doc comment,
    second line -/
    a
  | b

class inductive ClassInductive : Type where
  | -- c3
    /--
    first line of the doc comment,
    second line
    -/
    a : ClassInductive

-- A block comment, a doc comment on one line and a comment after the doc comment keep their place.
inductive OtherComments where
  | /- c4 -/
    /--
    first line of the doc comment,
    second line
    -/
    a
  | -- c5
    /-- a doc comment on one line -/
    b
  | /--
    first line of the doc comment,
    second line
    -/ -- c6
    c
