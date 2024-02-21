open Std BitVec
def f4 (v : Std.BitVec 32) : Nat :=
  match v with
  | 10#20 ++ 0#12  => 0 -- Should be rejected since `++` does not have `[match_pattern]`
  | _ => 1
