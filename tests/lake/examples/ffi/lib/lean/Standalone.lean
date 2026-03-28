@[extern "my_add"]
opaque myAdd : UInt32 → UInt32 → UInt32

@[extern "my_lean_fun"]
opaque myLeanFun : IO String

def main : IO Unit := do
  IO.println (myAdd 1 2)
  IO.println (← myLeanFun)
