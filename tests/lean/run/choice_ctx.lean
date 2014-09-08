import data.nat.basic
open nat
open eq
set_option pp.coercions true

namespace foo
theorem trans {a b c : nat} (H1 : a = b) (H2 : b = c) : a = c :=
trans H1 H2
end foo

open foo

theorem tst (a b : nat) (H0 : b = a) (H : b = 0) : a = 0
:= have H1 : a = b, from symm H0,
   trans H1 H

definition f (a b : nat) :=
let x := 3 in
a + x
