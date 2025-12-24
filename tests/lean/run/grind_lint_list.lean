import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! `List` exceptions -/

-- TODO: Not sure what to do here, see https://lean-fro.zulipchat.com/#narrow/channel/503415-grind/topic/.60.23grind_lint.60.20command/near/556730710
-- #grind_lint inspect List.getLast?_concat
#grind_lint skip List.getLast?_concat

-- `List.getLast?_pmap` is reasonable at 31.
#guard_msgs in
#grind_lint inspect (min := 31) List.getLast?_pmap

-- `List.replicate_sublist_iff` is reasonable at 30.
#guard_msgs in
#grind_lint inspect (min := 30) List.replicate_sublist_iff

-- `List.Sublist.append` is reasonable at 25.
#guard_msgs in
#grind_lint inspect (min := 25) List.Sublist.append

-- `List.Sublist.middle` is reasonable at 25.
#guard_msgs in
#grind_lint inspect (min := 25) List.Sublist.middle

/-! Check List namespace: -/

#guard_msgs in
#grind_lint check (min := 20) in List
