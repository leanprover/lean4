import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! `BitVec` exceptions -/

/-! Check BitVec namespace: -/

#guard_msgs in
#grind_lint inspect (min := 21) BitVec.msb_extractLsb

#guard_msgs in
#grind_lint inspect (min := 21) BitVec.msb_signExtend

#guard_msgs in
#grind_lint inspect (min := 21) BitVec.toInt_shiftLeftZeroExtend

#guard_msgs in
#grind_lint check  (min := 20) in BitVec

