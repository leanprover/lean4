import logic algebra.function
open function bool


constant f : num → bool
constant g : num → num

check f ∘ g ∘ g

check typeof id : num → num

constant h : num → bool → num

check swap h
check swap h ff num.zero

check typeof swap h ff num.zero : num

constant f1 : num → num → bool
constant f2 : bool → num

check (f1 on f2) ff tt
