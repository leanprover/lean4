/-!
Tests that string equality/inequality simprocs produce kernel-efficient proofs.

Previously, `String.reduceNe` and `String.reduceEq` used `decide` with `String.decEq`, which
forced the kernel to run UTF-8 encoding/decoding and byte array comparison. This caused a high
number of kernel unfoldings (e.g. 86 for `List.rec` on short strings).

The fix uses `String.ofList_injective` to reduce to `List Char` comparison, which is much
cheaper in the kernel since string literals are `String.ofList [chars]` at the kernel level.
-/

-- String.reduceNe: different strings (the primary use case)
-- Kernel should NOT unfold ByteArray/utf8 functions
set_option diagnostics true in
set_option diagnostics.threshold 16 in
/-- -/
#guard_msgs in
example : "hello" ≠ "foo" := by simp

-- String.reduceNe: equal strings
set_option diagnostics true in
set_option diagnostics.threshold 16 in
/-- -/
#guard_msgs in
example : "hello" ≠ "hello" ↔ False := by simp

-- String.reduceEq: equal strings
set_option diagnostics true in
set_option diagnostics.threshold 16 in
/-- -/
#guard_msgs in
example : "hello" = "hello" := by simp

-- String.reduceEq: different strings
set_option diagnostics true in
set_option diagnostics.threshold 16 in
/-- -/
#guard_msgs in
example : "hello" = "foo" ↔ False := by simp

-- Corner case: empty string vs nonempty
set_option diagnostics true in
set_option diagnostics.threshold 16 in
/-- -/
#guard_msgs in
example : "" ≠ "a" := by simp

set_option diagnostics true in
set_option diagnostics.threshold 16 in
/-- -/
#guard_msgs in
example : "a" ≠ "" := by simp

-- Corner case: one string is a prefix of the other
set_option diagnostics true in
set_option diagnostics.threshold 16 in
/-- -/
#guard_msgs in
example : "foo" ≠ "foobar" := by simp

set_option diagnostics true in
set_option diagnostics.threshold 16 in
/-- -/
#guard_msgs in
example : "foobar" ≠ "foo" := by simp
