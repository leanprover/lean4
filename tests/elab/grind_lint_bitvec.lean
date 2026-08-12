import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! `BitVec` exceptions -/

/-
**Note for Kim**: the instantiation chains behind the limits below are now dominated by the
`msb`/`getMsbD` representation-bridging lemmas (`msb_eq_getMsbD_zero`,
`msb_eq_false_iff_two_mul_lt`, `getMsbD_of_ge`, `getMsbD_last`, `getMsbD_eq_getElem`).
Each `msb`-related instance cascades through the representation changes
(`msb` → `getMsbD` → `getElem` → `toNat`), so every theorem touching `msb` pays the whole
chain. Worth reviewing whether all these bridges need `[grind =]`, or whether `grind`
should commit to one canonical representation and reach the others on demand.
-/

/-! Check BitVec namespace: -/

#guard_msgs in
#grind_lint inspect (min := 22) BitVec.msb_extractLsb

#guard_msgs in
#grind_lint inspect (min := 21) BitVec.msb_signExtend

#guard_msgs in
#grind_lint inspect (min := 24) BitVec.toInt_shiftLeftZeroExtend

#guard_msgs in
#grind_lint check  (min := 24) in BitVec
