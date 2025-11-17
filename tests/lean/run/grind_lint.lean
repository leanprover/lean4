-- Already working:

#guard_msgs in
#grind_lint check (min := 20) in Array

-- In progress:

-- TODO: Not sure what to do here, see https://lean-fro.zulipchat.com/#narrow/channel/503415-grind/topic/.60.23grind_lint.60.20command/near/556730710
#grind_lint inspect List.getLast?_concat
#grind_lint skip List.getLast?_concat

-- TODO: We should consider changing the grind annotation for `List.getElem?_eq_none`
-- so it only fires if we've already proved the hypothesis holds. (i.e. the new gadget)
-- Other than that, everything looks sane here:
#grind_lint inspect List.getLast?_pmap
#grind_lint skip List.getLast?_pmap


-- TODO: `List.Sublist.eq_of_length` should probably only fire when we've already proved the hypotheses.

-- `List.replicate_sublist_iff` is reasonable at 30.
#guard_msgs in
#grind_lint inspect (min := 30) List.replicate_sublist_iff
#grind_lint skip List.replicate_sublist_iff

-- `List.Sublist.append` is reasonable at 25.
#guard_msgs in
#grind_lint inspect (min := 25) List.Sublist.append
#grind_lint skip List.Sublist.append

-- `List.Sublist.middle` is reasonable at 25.
#guard_msgs in
#grind_lint inspect (min := 25) List.Sublist.middle
#grind_lint skip List.Sublist.middle

#grind_lint check (min := 20) in List

-- TODO:

-- #grind_lint check (min := 20) in Vector
-- #grind_lint check (min := 20) in Option
-- #grind_lint check (min := 20) in Nat Int Rat Dyadic
-- #grind_lint check (min := 20) in Prod Sum
-- #grind_lint check (min := 20) in module Std
-- #grind_lint check (min := 20)
