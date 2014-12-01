prelude
constant nat : Type.{1}
constant f : nat → nat

namespace foo
  constant int : Type.{1}
  constant f   : int → int
  constant a   : nat
  constant i   : int
  check _root_.f a
  check f i
end foo

open foo
constants a : nat
constants i : int
check f a
check f i
