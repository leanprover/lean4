def check_eq {α} [BEq α] [Repr α] (tag : String) (expected actual : α) : IO Unit :=
  unless (expected == actual) do
    throw $ IO.userError $
      s!"assertion failure \"{tag}\":\n  expected: {repr expected}\n  actual:   {repr actual}"

def DecodeUTF8: IO Unit := do
  let str := "Hello, 英語!"
  let cs := String.toList str
  let ns := cs.map Char.toNat
  IO.println cs
  IO.println ns
  check_eq "utf-8 chars" [72, 101, 108, 108, 111, 44, 32, 33521, 35486, 33] ns
  check_eq "utf-8 bytes" #[72, 101, 108, 108, 111, 44, 32, 232, 139, 177, 232, 170, 158, 33] str.toUTF8.data
  check_eq "string eq" (some str) (String.fromUTF8? str.toUTF8)

#eval DecodeUTF8
