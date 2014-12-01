prelude
constant int : Type.{1}
constant nat : Type.{1}
namespace int
constant plus : int → int → int
end int

namespace nat
constant plus : nat → nat → nat
end nat

open int nat

constants a b : int


check plus a b

constant f : int → int → int
constant g : nat → nat → int
notation A `+`:65 B:65 := f A (g B B)
constant n : nat
check a + n
