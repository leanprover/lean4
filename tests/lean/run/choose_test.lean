import data.encodable
open nat encodable

theorem ex : ∃ x : nat, x > 3 :=
exists.intro 6 dec_trivial

reveal ex

eval choose ex

example : choose ex = 4 :=
rfl
