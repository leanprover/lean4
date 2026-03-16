/--
error: `main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`
-/
#guard_msgs in
def main (_ : List String) : UInt32 := 0
