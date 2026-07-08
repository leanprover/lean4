def showChars : Nat → String → String.Pos.Raw → IO Unit
| 0,     _, _   => pure ()
| n+1,   s, idx => do
  unless idx.atEnd s  do
    IO.println (">> " ++ toString (idx.get s)) *>
    showChars n s (idx.next s)

def main : IO UInt32 :=
let s₁             := "hello α_world_β";
let b : String.Pos.Raw := 0;
let e              := s₁.rawEndPos;
IO.println (b.extract s₁ e) *>
IO.println ((b+ "  ").extract s₁ e) *>
IO.println ((b+ "  ").extract s₁ (e.unoffsetBy ⟨1⟩)) *>
IO.println ((b.offsetBy ⟨2⟩).extract s₁ (e.unoffsetBy ⟨2⟩)) *>
IO.println ((b.offsetBy ⟨7⟩).extract s₁ e) *>
IO.println ((b.offsetBy ⟨8⟩).extract s₁ e) *>
IO.println (toString e) *>
IO.println (repr "   aaa   ".trimAscii.copy) *>
showChars s₁.length s₁ 0  *>
IO.println ("abc".isPrefixOf "abcd") *>
IO.println ("abcd".isPrefixOf "abcd") *>
IO.println ("".isPrefixOf "abcd") *>
IO.println ("".isPrefixOf "") *>
IO.println ("ab".isPrefixOf "cb") *>
IO.println ("ab".isPrefixOf "a") *>
IO.println ("αb".isPrefixOf "αbc") *>
IO.println ("\x00a").length *>
pure 0
