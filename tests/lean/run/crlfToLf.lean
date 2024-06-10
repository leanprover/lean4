/-!
# Test `String.crlfToLf`
-/

/-!
Leaves single `\n`'s alone.
-/
/-- info: "hello\nworld" -/
#guard_msgs in #eval String.crlfToLf "hello\nworld"

/-!
Turns `\r\n` into `\n`.
-/
/-- info: "hello\nworld" -/
#guard_msgs in #eval String.crlfToLf "hello\r\nworld"

/-!
In a string of `\r...\r\n`, only normalizes the last `\r\n`.
-/
/-- info: "hello\x0d\nworld" -/
#guard_msgs in #eval String.crlfToLf "hello\r\r\nworld"

/-!
Two in a row.
-/
/-- info: "hello\n\nworld" -/
#guard_msgs in #eval String.crlfToLf "hello\r\n\r\nworld"

/-!
Normalizes at the end.
-/
/-- info: "hello\nworld\n" -/
#guard_msgs in #eval String.crlfToLf "hello\r\nworld\r\n"

/-!
Can handle a loose `\r` as the last character.
-/
/-- info: "hello\nworld\x0d" -/
#guard_msgs in #eval String.crlfToLf "hello\r\nworld\r"
