prelude
import Init.Guard
import Init.WFComputable

-- Test wellfounded fix call is executable
def log2p1 : Nat → Nat :=
  WellFounded.fix Nat.lt_wfRel.2 fun n IH =>
    let m := n / 2
    if h : m < n then
      IH m h + 1
    else
      0

#guard log2p1 4 == 3
