/--
error: `main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`
-/
#guard_msgs in
def main (args : List ByteArray) : IO Unit := pure ()
