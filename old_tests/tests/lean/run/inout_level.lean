section bug
variables (x y z : Type)
variables (f : x → y) (g : y → z)
variables (xy : set (x → y)) (yz : set (y → z)) (xz : set (x → z))
--#check f ∈ xy
--#check g ∈ yz
#check (g ∘ f) ∈ xz --error
end bug
