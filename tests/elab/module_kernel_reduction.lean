module

/-!
Kernel reduction of `decide` / `rfl` under the module system.

Three separate exposure gaps used to stall reduction across a module boundary:

* `Array.instDecidableEq` delegates its nonempty/nonempty case to
  `Array.instDecidableEqImpl`;
* every `deriving DecidableEq` instance delegates to a generated `decEq`;
* `Array.ofFn` delegates to its `ofFn.go` auxiliary.

In each case the callee was a plain `def`, so its body was unavailable downstream
and reduction got stuck. Exposing the callee (for `ofFn.go`, by exposing `ofFn`,
which covers its `where` auxiliaries) restores reduction.
-/

-- `Array` equality, both sides nonempty.
example : (#[0, 1] : Array Nat) ≠ #[1] := by decide
example : (#[2, 3] : Array Nat) = #[2, 3] := by decide
example : ¬ ((#[0, 1] : Array Nat) = #[1, 0]) := by decide
example : decide ((#[0, 1] : Array Nat) = #[0, 1]) = true := by rfl
example : (#[1, 2, 3] : Array Nat) ≠ #[1, 2, 4] := by decide +kernel

-- Cases that already reduced, kept as regression coverage.
example : (#[] : Array Nat) = #[] := by decide
example : (#[] : Array Nat) ≠ #[1] := by decide

-- `Vector`, whose `DecidableEq` is derived.
example : (#v[0, 1, 2] : Vector Nat 3) ≠ #v[0, 0, 0] := by decide
example : (#v[0, 1, 2] : Vector Nat 3) = #v[0, 1, 2] := by decide +kernel

-- `Array.ofFn` and `Vector.ofFn`.
example : (Array.ofFn (n := 3) (fun i => i.val)).size = 3 := by decide
example : Array.ofFn (n := 3) (fun i => i.val) = #[0, 1, 2] := by decide
example : Vector.ofFn (n := 3) (fun i => i.val) = #v[0, 1, 2] := by decide
