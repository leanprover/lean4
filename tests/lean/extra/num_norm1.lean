import algebra.numeral algebra.ring
open algebra

variable {A : Type}
variable [s : ring A]
include s

example : add (bit0 (one:A)) one = bit1 one :=
begin
  norm_num
end
