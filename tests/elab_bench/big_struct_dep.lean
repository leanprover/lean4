set_option maxRecDepth 1_000_000
set_option maxHeartbeats 0

inductive T : Nat → Type where
  | mk : {n : Nat} → T n

structure M where
  b0 : Nat
  b1 : T b0 → Nat
  b2 : T (b1 .mk) → Nat
  b3 : T (b2 .mk) → Nat
  b4 : T (b3 .mk) → Nat
  b5 : T (b4 .mk) → Nat
  b6 : T (b5 .mk) → Nat
  b7 : T (b6 .mk) → Nat
  b8 : T (b7 .mk) → Nat
  b9 : T (b8 .mk) → Nat
  b10 : T (b9 .mk) → Nat
  b11 : T (b10 .mk) → Nat
  b12 : T (b11 .mk) → Nat
  b13 : T (b12 .mk) → Nat
  b14 : T (b13 .mk) → Nat
  b15 : T (b14 .mk) → Nat
  b16 : T (b15 .mk) → Nat
  b17 : T (b16 .mk) → Nat
  b18 : T (b17 .mk) → Nat
  b19 : T (b18 .mk) → Nat
  b20 : T (b19 .mk) → Nat
  b21 : T (b20 .mk) → Nat
  b22 : T (b21 .mk) → Nat
  b23 : T (b22 .mk) → Nat
  b24 : T (b23 .mk) → Nat
  b25 : T (b24 .mk) → Nat
  b26 : T (b25 .mk) → Nat
  b27 : T (b26 .mk) → Nat
  b28 : T (b27 .mk) → Nat
  b29 : T (b28 .mk) → Nat
  b30 : T (b29 .mk) → Nat
  b31 : T (b30 .mk) → Nat
  b32 : T (b31 .mk) → Nat
  b33 : T (b32 .mk) → Nat
  b34 : T (b33 .mk) → Nat
  b35 : T (b34 .mk) → Nat
  b36 : T (b35 .mk) → Nat
  b37 : T (b36 .mk) → Nat
  b38 : T (b37 .mk) → Nat
  b39 : T (b38 .mk) → Nat
  b40 : T (b39 .mk) → Nat
