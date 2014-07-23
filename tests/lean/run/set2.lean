import standard bool
using bool

namespace set

definition set (T : Type) := T → bool
definition mem {T : Type} (a : T) (s : set T) := s a = '1
infix `∈`:50 := mem

section
  parameter {T : Type}

  definition empty : set T := λx, '0
  notation `∅` := empty

  theorem mem_empty (x : T) : ¬ (x ∈ ∅)
  := not_intro (λH : x ∈ ∅, absurd H b0_ne_b1)
end