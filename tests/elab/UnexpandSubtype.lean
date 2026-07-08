set_option pp.analyze false

set_option pp.funBinderTypes false in
#check { x : Nat // x < 10 }

set_option pp.funBinderTypes true in
#check { x : Nat // x < 10 }
