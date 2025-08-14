structure DepThing {α : Type u} (l : List α) : Type u where
  suffix : List α
  property : suffix = l

example (n : Nat) (c : DepThing (List.range' 1 (n/1))) (h : 0 < c.suffix.length) : True :=  by
  grind
