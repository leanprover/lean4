import data.stream
open nat

namespace stream
variable A : Type

set_option pp.beta false

theorem mem_of_mem_odd₂ (a : A) (s : stream A) : a ∈ odd s → a ∈ s :=
assume ainos, obtain n (h : a = nth n (odd s)), from ainos,
exists.intro (2*n+1) (by rewrite [h, nth_odd])

end stream
