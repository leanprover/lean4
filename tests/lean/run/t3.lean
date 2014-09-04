variable int : Type.{1}
variable nat : Type.{1}
namespace int
variable plus : int → int → int
end int

namespace nat
variable plus : nat → nat → nat
end nat

open int nat

variables a b : int


check plus a b

variable f : int → int → int
variable g : nat → nat → int
notation A `+`:65 B:65 := f A (g B B)
variable n : nat
check a + n
