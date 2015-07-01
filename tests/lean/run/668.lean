set_option pp.coercions true

namespace Nat
  constant Nat : Type₁
  constant num2Nat : num → Nat
  attribute num2Nat [coercion]
  check (0 : Nat)
end Nat

constant Int : Type₁

namespace Int
  open Nat
  constant Nat2Int : Nat → Int
  attribute Nat2Int [coercion]
  check (0 : Int)
end Int

open Int
check (0 : Int)
