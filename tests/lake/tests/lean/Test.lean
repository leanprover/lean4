import Lib

def main (args : List String) : IO Unit :=
  IO.println s!"Hello {", ".intercalate args}!"

#eval IO.println s!"Hello from {libSrc}!"
