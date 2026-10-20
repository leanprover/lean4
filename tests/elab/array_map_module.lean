module

/-!
Tests kernel reduction of `Array.map` across a module boundary.
-/

example : ((#[1, 2] : Array Nat).map (· + 1)).toList = [2, 3] := by decide +kernel
example : ((#[] : Array Nat).map (· + 1)).toList = [] := by decide +kernel
example : ((#v[1, 2] : Vector Nat 2).map (· + 1)).toList = [2, 3] := by decide +kernel
