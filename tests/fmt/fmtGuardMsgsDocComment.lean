module

/-!
Tests that the formatter keeps the text of the doc comment of `#guard_msgs` as it is, apart from
whitespace at its ends: `#guard_msgs` compares this text with the messages of the command, so the
indentation of its lines must not change.
-/

-- The continuation line is indented relative to the first line, which starts after `/--`.
/-- info: a
  b -/
#guard_msgs in
#eval IO.println "a\n  b"

-- The indentation of the doc comment itself is part of the text, and the command moves to column 0.
namespace Indented
  /--
    info: a
  b
  -/
  #guard_msgs in
  #eval IO.println "a\n  b"
end Indented

-- Whitespace at the ends of the text does not count.
/--   info: a
  b

   -/
#guard_msgs (substring := true) in
#eval IO.println "a\n  b"

/-- info: 1 -/
#guard_msgs in
#eval 1

-- Other doc comments are still normalized.
/-- A doc comment
    with an indented second line. -/
def f := 1
