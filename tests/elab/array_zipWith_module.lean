module

/-!
Tests kernel reduction of `Array.zipWith` across a module boundary.
-/

example : (Array.zipWith (· + ·) #[1, 2, 3] #[10, 20]).toList = [11, 22] := by
  decide +kernel

example : (Array.zipWith (· + ·) (#[] : Array Nat) #[10, 20]).toList = [] := by
  decide +kernel

example : (Vector.zipWith (· + ·) #v[1, 2] #v[10, 20]).toList = [11, 22] := by
  decide +kernel
