#check @epsilon -- Error

noncomputable def foo1 (f g : Nat → Nat) : Nat :=
  if f = g then 1 else 2 -- Error

section
open Classical

#check @epsilon

noncomputable def foo2 (f g : Nat → Nat) : Nat :=
  if f = g then 1 else 2 -- Ok
end

#check @epsilon -- Error

section

open scoped Classical
#check @epsilon -- Error

noncomputable def foo3 (f g : Nat → Nat) : Nat :=
  if f = g then 1 else 2 -- Ok

end
