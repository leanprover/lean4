import Lean
/-!
# `_` separators for numeric literals
RFC: https://github.com/leanprover/lean4/issues/6199
-/
set_option pp.mvars false

open Lean Elab

elab "#term " s:str : command => Command.liftTermElabM <| withRef s do
  let t ← Lean.ofExcept <| Parser.runParserCategory (← getEnv) `term s.getString
  let e ← Term.elabTermAndSynthesize t none
  logInfo m!"{e} : {← Meta.inferType e}"

/-!
Decimal tests
-/
/-- info: 0 : Nat -/
#guard_msgs in #term "0"
/-- info: 1 : Nat -/
#guard_msgs in #term "1"
/-- info: 1000000 : Nat -/
#guard_msgs in #term "1000000"
/-- info: 1000000 : Nat -/
#guard_msgs in #term "1_000_000"
/-- info: 1000000 : Nat -/
#guard_msgs in #term "1__000___000"
/-- error: <input>:1:5: unexpected end of input; expected decimal number -/
#guard_msgs in #term "1_00_"
/-- error: <input>:1:6: unexpected character; expected decimal number -/
#guard_msgs in #term "(1_00_)"
-- Starting with `_` is an identifier:
/--
error: unknown identifier '_10'
---
info: sorry : ?_
-/
#guard_msgs in #term "_10"

/-!
Scientific tests
-/
/-- info: 100000. : Float -/
#guard_msgs in #term "100_000."
/-- info: 100000.0 : Float -/
#guard_msgs in #term "100_000.0"
/-- info: 0. : Float -/
#guard_msgs in #term "0."
-- The decimal parser requires a digit at the start, so the `_` is left over:
/-- error: <input>:1:4: expected end of input -/
#guard_msgs in #term "100._"
/-- info: 100.111111 : Float -/
#guard_msgs in #term "100.111_111"
/-- error: <input>:1:8: unexpected end of input; expected decimal number -/
#guard_msgs in #term "100.111_"
/-- error: <input>:1:9: unexpected character; expected decimal number -/
#guard_msgs in #term "(100.111_)"
/-- info: 100111111e1094 : Float -/
#guard_msgs in #term "100.111_111e1_100"
/-- error: <input>:1:5: unexpected end of input; expected decimal number -/
#guard_msgs in #term "1e10_"
/-- error: <input>:1:6: unexpected character; expected decimal number -/
#guard_msgs in #term "(1e10_)"
/-- error: <input>:1:1: missing exponent digits in scientific literal -/
#guard_msgs in #term "1e_10"

/-!
Base-2 tests
-/
/-- info: 15 : Nat -/
#guard_msgs in #term "0b1111"
/-- info: 15 : Nat -/
#guard_msgs in #term "0b11_11"
/-- info: 15 : Nat -/
#guard_msgs in #term "0b__11__11"
/-- error: <input>:1:7: unexpected end of input; expected binary number -/
#guard_msgs in #term "0b1111_"
/-- error: <input>:1:8: unexpected character; expected binary number -/
#guard_msgs in #term "(0b1111_)"

/-!
Base-8 tests
-/
/-- info: 512 : Nat -/
#guard_msgs in #term "0o1000"
/-- info: 512 : Nat -/
#guard_msgs in #term "0o1_000"
/-- info: 512 : Nat -/
#guard_msgs in #term "0o_1_000"
/-- error: <input>:1:7: unexpected end of input; expected octal number -/
#guard_msgs in #term "0o1000_"
/-- error: <input>:1:8: unexpected character; expected octal number -/
#guard_msgs in #term "(0o1000_)"

/-!
Base-16 tests
-/
/-- info: 4096 : Nat -/
#guard_msgs in #term "0x1000"
/-- info: 4096 : Nat -/
#guard_msgs in #term "0x1_000"
/-- info: 4096 : Nat -/
#guard_msgs in #term "0x_1_000"
/-- error: <input>:1:7: unexpected end of input; expected hexadecimal number -/
#guard_msgs in #term "0x1000_"
/-- error: <input>:1:8: unexpected character; expected hexadecimal number -/
#guard_msgs in #term "(0x1000_)"
