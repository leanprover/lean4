@[extern "my_add"]
constant myAdd : UInt32 → UInt32 → UInt32

def main : IO Unit :=
  IO.println <| myAdd 1 2
