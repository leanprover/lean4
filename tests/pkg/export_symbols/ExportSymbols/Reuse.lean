module

import all ExportSymbols.Basic

/-!
Requests the same specialization as `specializingFn` with access to the private scope of `Basic`,
see `run_test.sh`.
-/

@[noinline] public def reusingFn (xs : List Nat) (y : UInt8) : Nat :=
  xs.foldl (fun acc x => acc + x * y.toNat) 0 + 1
