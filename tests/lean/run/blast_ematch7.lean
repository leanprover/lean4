import algebra.ring data.int
open algebra

variables {A : Type} [s : ring A] (a b : A)
include s

set_option blast.subst  false
set_option blast.simp   false
set_option blast.ematch true
attribute zero_mul [forward]

example : a = 0 → a * b = 0 :=
by blast

open int

-- Remark: int is a non-recursive datatype. So, the recursor action will
-- destruct it. This is a dumb move, and we need to prove the same theorem 4 times because of that.
-- It also demonstrates we need better heuristics for the recursor action and/or annotations.
set_option blast.recursor false

definition ex1 (a b : int) : a = 0 → a * b = 0 :=
by blast

print ex1
