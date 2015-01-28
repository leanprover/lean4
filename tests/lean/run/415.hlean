import algebra.group
open path_algebra

variable {A : Type}
variable [s : add_comm_group A]
include s

theorem add_minus_cancel_left1 (a b c : A) : (c + a) - (c + b) = a - b :=
begin
  rotate_left 1,
  apply sorry
end

theorem add_minus_cancel_left2 (a b c : A) : (c + a) - (c + b) = a - b :=
by rotate_left 1;
   apply sorry
