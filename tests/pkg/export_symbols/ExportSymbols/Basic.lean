module

/-!
Functions of each visibility for checking which native symbols are exported, see `run_test.sh`.
All take a `UInt8` so that each has a boxed variant.
-/

@[noinline] private def privateFn (x : Nat) (y : UInt8) : Nat := x + y.toNat

@[noinline] def moduleLocalFn (x : Nat) (y : UInt8) : Nat := x * y.toNat

public def publicFn (x : Nat) (y : UInt8) : Nat := privateFn x y + moduleLocalFn x y

@[export export_symbols_exported] private def exportedFn (x : Nat) (y : UInt8) : Nat := x - y.toNat

public meta def metaFn (x : Nat) (y : UInt8) : Nat := x + y.toNat + 1

/-- Creates a specialization of `List.foldl` that `Reuse` has in its specialization cache. -/
@[noinline] def specializingFn (xs : List Nat) (y : UInt8) : Nat :=
  xs.foldl (fun acc x => acc + x * y.toNat) 0
