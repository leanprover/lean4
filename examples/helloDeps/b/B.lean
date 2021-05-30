import A
import B.Bar
import B.Baz

def main : IO Unit :=
  IO.println s!"Hello, {foo} {name}!"
