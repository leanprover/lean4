module

/-!
Tests wasm32 constructor allocation, scalar fields, projection, and reference counting.
-/

inductive Pair where
  | mk : UInt32 → UInt32 → Pair

@[noinline] def sumPair : Pair → UInt32
  | .mk x y => x + y

@[export lean_wasm_object_sum]
def objectSum (x y : UInt32) : UInt32 :=
  sumPair (.mk x y)
