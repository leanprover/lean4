-- Test that pattern matching on the `String.ofByteArray` constructor works correctly
-- at runtime.

def getBytes (s : String) : ByteArray :=
  match s with
  | ⟨bs, _⟩ => bs

#eval getBytes "hello" |>.size
#eval getBytes "" |>.size
#eval getBytes "α" |>.size
