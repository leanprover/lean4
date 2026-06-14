/-!
EmitZig test: pattern matching on constructors.
-/
inductive Color where
  | red | green | blue

def colorName : Color → String
  | .red => "red"
  | .green => "green"
  | .blue => "blue"

def main : IO Unit :=
  IO.println (colorName .green)
