import function logic num bool
using function num bool


variable f : num → bool
variable g : num → num

check f ∘ g ∘ g

check typeof id : num → num
check num → num ⟨is_typeof⟩ id

variable h : num → bool → num

check flip h
check flip h '0 zero

check typeof flip h '0 zero : num

variable f1 : num → num → bool
variable f2 : bool → num

check (f1 on f2) '0 '1
