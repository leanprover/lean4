module

/-!
Tests kernel reduction of `Array.modify` across a module boundary.
-/

example : ((#[1, 2] : Array Nat).modify 0 (· + 10)).toList = [11, 2] := by
  decide +kernel

example : ((#[1, 2] : Array Nat).modify 3 (· + 10)).toList = [1, 2] := by
  decide +kernel

example :
    (Id.run ((#[1, 2] : Array Nat).modifyM 1 (fun x => pure (x + 10)))).toList = [1, 12] := by
  decide +kernel
