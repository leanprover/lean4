module

/-!
Shared pure library for the core-runtime multi-module WebAssembly test.
Only uses the language-core object model (constructors, RC, scalars) — no IO.
-/

public inductive CorePair where
  | mk : UInt32 → UInt32 → CorePair

@[noinline] public def corePairSum : CorePair → UInt32
  | .mk x y => x + y

@[noinline] public def corePairScale (p : CorePair) (k : UInt32) : CorePair :=
  match p with
  | .mk x y => .mk (x * k) (y * k)
