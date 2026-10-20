module

/-!
`Array.back`, `Array.back!`, and `Array.back?` are `@[expose]`, so a
downstream `module` can reduce them under `decide` (and the kernel), exactly
like the `getElem?`/`size` accessors they are defined in terms of. Without
the attribute their bodies do not cross the module boundary and the `decide`
calls below get stuck on the unreduced application.
-/

-- Baseline: the accessors `back?` is built from already reduce.
example : (#[1, 2, 3] : Array Nat)[2]? = some 3 := by decide
example : (#[1, 2, 3] : Array Nat).size = 3 := by decide

-- The `back` family must reduce too.
example : (#[1, 2, 3] : Array Nat).back? = some 3 := by decide
example : (#[1, 2, 3] : Array Nat).back? = some 3 := by decide +kernel
example : (#[1, 2, 3] : Array Nat).back! = 3 := by decide
example : (#[1, 2, 3] : Array Nat).back = 3 := by decide
