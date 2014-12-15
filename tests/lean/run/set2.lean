import logic data.bool
open bool

namespace set

definition set (T : Type) := T → bool
definition mem {T : Type} (a : T) (s : set T) := s a = tt
infix `∈` := mem

section
  variable {T : Type}

  definition empty : set T := λx, ff
  notation `∅` := empty

  theorem mem_empty (x : T) : ¬ (x ∈ ∅)
  := not.intro (λH : x ∈ ∅, absurd H ff_ne_tt)
end

end set
