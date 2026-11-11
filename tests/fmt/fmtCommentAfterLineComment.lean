/-!
Tests that a comment is not appended to a line that already ends in a line comment, where it would
become part of that comment.
-/

def x : Nat -- a
  := 1 -- b

example : True -- c
    := by
  trivial -- d
