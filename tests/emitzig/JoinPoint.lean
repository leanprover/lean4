/-!
EmitZig test: join points arising from a `match` used in non-tail position.
-/
inductive Color where
  | red | green | blue

def colorName (c : Color) : String :=
  let s := match c with
    | Color.red => "red"
    | Color.green => "green"
    | Color.blue => "blue"
  s ++ "!"

def main : IO Unit :=
  IO.println (colorName Color.green)
