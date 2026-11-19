macro "co " x:ident : command => do
  `(coinductive $x : Prop where | ok)

/-- error: Coinductive predicates are not allowed inside of macro scopes -/
#guard_msgs in
co f

macro "co2" : command => do
  `(coinductive test : Prop where | ctor)

/-- error: Coinductive predicates are not allowed inside of macro scopes -/
#guard_msgs in
co2
