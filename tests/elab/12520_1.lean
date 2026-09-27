
structure T where
  val : Bool
  proof : True

variable (x : True → T)

example : (T.mk (x True.intro).val) = (fun h => x h) := rfl
example : (fun h => x h) = x := rfl
example : (T.mk (x True.intro).val) = x := rfl
