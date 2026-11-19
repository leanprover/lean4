module

/-!
Tests kernel reduction of `Array.ofFn` across a module boundary.
-/

example : (Array.ofFn (n := 3) (fun i => i.val)).size = 3 := by rfl
example : Array.ofFn (n := 3) (fun i => i.val) = #[0, 1, 2] := by rfl
example : Vector.ofFn (n := 3) (fun i => i.val) = #v[0, 1, 2] := by rfl
