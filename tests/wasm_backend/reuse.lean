module

/-!
Tests wasm32 join-point lowering through constructor uniqueness and reuse control flow.
-/

inductive Pair where
  | mk : UInt32 → UInt32 → Pair

@[noinline] def replaceFirst (p : Pair) (x : UInt32) : Pair :=
  match p with
  | .mk _ y => .mk x y

@[export lean_wasm_reuse]
def reuse (x y z : UInt32) : UInt32 :=
  match replaceFirst (.mk x y) z with
  | .mk a b => a + b
