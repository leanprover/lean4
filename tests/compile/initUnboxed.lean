initialize test : UInt64 ← pure 0
initialize testb : Bool ← pure false
initialize testu : USize ← pure 1
initialize testf : Float ← pure 0.5
initialize test32 : UInt32 ← pure 16

def main : IO Unit := do
  IO.println test
  IO.println testb
  IO.println testu
  IO.println testf
  IO.println test32
