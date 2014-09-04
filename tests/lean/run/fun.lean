import logic struc.function
open function bool


variable f : num → bool
variable g : num → num

check f ∘ g ∘ g

check typeof id : num → num
check num → num ⟨is_typeof⟩ id

variable h : num → bool → num

check flip h
check flip h ff num.zero

check typeof flip h ff num.zero : num

variable f1 : num → num → bool
variable f2 : bool → num

check (f1 on f2) ff tt
