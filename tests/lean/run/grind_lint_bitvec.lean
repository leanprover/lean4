import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! `BitVec` exceptions -/

-- `BitVec.msb_replicate` is reasonable at 25.
#guard_msgs in
#grind_lint inspect (min := 30) BitVec.msb_replicate

-- TODO: Reduce limit after we add support for `no_value` constraint
-- `BitVec.msb_signExtend` is reasonable at 22.
#guard_msgs in
#grind_lint inspect (min := 26)  BitVec.msb_signExtend

/-! Check BitVec namespace: -/

-- TODO: Reduce limit after we add support for `no_value` constraint. It was `20`
#guard_msgs in
#grind_lint check (min := 23) in BitVec
