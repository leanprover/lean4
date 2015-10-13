set_option pp.coercions true

namespace Nat
  constant Nat : Type₁
  constant num2Nat : num → Nat
  attribute num2Nat [coercion]
  definition foo : Nat := (0:num)
end Nat

constant Int : Type₁

namespace Int
  open Nat
  constant Nat2Int : Nat → Int
  attribute Nat2Int [coercion]
  definition foo : Int := (0:num)
end Int

open Int
definition foo : Int := (0:num)
