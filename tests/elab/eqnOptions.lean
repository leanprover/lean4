/-! Tests that options affecting equational theorems work as expected. -/

namespace Test1
def nonrecfun : Bool → Nat
  | false => 0
  | true => 0

/--
info: equations:
@[defeq] theorem Test1.nonrecfun.eq_1 : nonrecfun false = 0
@[defeq] theorem Test1.nonrecfun.eq_2 : nonrecfun true = 0
-/
#guard_msgs in
#print equations nonrecfun

end Test1

namespace Test2

set_option backward.eqns.nonrecursive false in
def nonrecfun : Bool → Nat
  | false => 0
  | true => 0

/--
info: equations:
@[defeq] theorem Test2.nonrecfun.eq_1 : ∀ (x : Bool),
  nonrecfun x =
    match x with
    | false => 0
    | true => 0
-/
#guard_msgs in
#print equations nonrecfun

end Test2

namespace Test3

def nonrecfun : Bool → Nat
  | false => 0
  | true => 0

-- should have no effect
set_option backward.eqns.nonrecursive false

/--
info: equations:
@[defeq] theorem Test3.nonrecfun.eq_1 : nonrecfun false = 0
@[defeq] theorem Test3.nonrecfun.eq_2 : nonrecfun true = 0
-/
#guard_msgs in
#print equations nonrecfun

end Test3
