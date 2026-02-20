structure Point where
  x : Int
  y : Int

def foo (inputs : List Point) : (Float × Float) :=
  (0.0, 0.0)

#eval foo ⟨0, 0⟩
