import data.stream
open nat

namespace stream
variable A : Type

theorem mem_cons_of_mem₂ {a : A} {s : stream A} (b : A) : a ∈ s → a ∈ b :: s :=
assume ains, obtain n h, from ains,
exists.intro (succ n) begin rewrite [nth_succ, tail_cons, h] end

end stream
