/-! regression test for use after free on lean_string_extract -/

def hugeEnd : String.Pos.Raw := ⟨2^70⟩
@[noinline] def trim (s : String) := String.Pos.Raw.extract s ⟨1⟩ hugeEnd
@[noinline] def heap (s : String) := s ++ "-heap-padding"

def fill : Nat → Array String → Array String
  | 0, a => a
  | n+1, a => fill n (a.push (heap (toString (n % 10))))

def main (args : List String) : IO Unit := do
  let stale := trim (heap args[0]!)
  let replacements := fill 64 #[]
  IO.println (replacements[63]! ++ "|" ++ stale)
