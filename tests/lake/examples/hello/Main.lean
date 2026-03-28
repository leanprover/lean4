import Hello

def main (args : List String) : IO Unit :=
  if args.isEmpty then
    IO.println s!"Hello, {hello}!"
  else
    IO.println s!"Hello, {", ".intercalate args}!"
