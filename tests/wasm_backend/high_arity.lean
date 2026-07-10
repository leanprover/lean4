module

/-!
Tests high-arity closure application via `lean_wasm_apply_m` (arity > 16).
-/

abbrev F17 :=
  UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 →
  UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32

@[noinline] def sum17 (a b c d e f g h i j k l m n o p q : UInt32) : UInt32 :=
  a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q

@[noinline] def call17 (fn : F17) : UInt32 :=
  fn 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1

@[export lean_wasm_high_arity]
def highArity : UInt32 :=
  call17 sum17
