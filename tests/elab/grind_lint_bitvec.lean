import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! `BitVec` exceptions -/

-- `BitVec.msb_replicate` is reasonable at 25.
#guard_msgs in
#grind_lint inspect (min := 30) BitVec.msb_replicate

-- `BitVec.msb_signExtend` is reasonable at 26.
#guard_msgs in
#grind_lint inspect (min := 26) BitVec.msb_signExtend

/-! Check BitVec namespace: -/

#guard_msgs in
#grind_lint check (min := 23) in BitVec
