import standard
using bool

namespace set

definition set (T : Type) := T → bool
definition mem {T : Type} (a : T) (s : set T) := s a = tt
infix `∈`:50 := mem

section
  parameter {T : Type}

  definition empty : set T := λx, ff
  notation `∅` := empty

  theorem mem_empty (x : T) : ¬ (x ∈ ∅)
  := not_intro (λH : x ∈ ∅, absurd H ff_ne_tt)
end