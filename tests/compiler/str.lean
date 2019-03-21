def showChars : Nat → String → String.utf8Pos → IO Unit
| 0     _ _   := pure ()
| (n+1) s idx :=
  unless (s.utf8AtEnd idx) $
    IO.println (">> " ++ toString (s.utf8Get idx)) *>
    showChars n s (s.utf8Next idx)

def main : IO UInt32 :=
let s₁ := "hello α_world_β" in
let b  := String.utf8Begin in
let e  := s₁.utf8ByteSize in
IO.println (s₁.extract b e) *>
IO.println (s₁.extract (b+2) e) *>
IO.println (s₁.extract (b+2) (e-1)) *>
IO.println (s₁.extract (b+2) (e-2)) *>
IO.println (s₁.extract (b+7) e) *>
IO.println (s₁.extract (b+8) e) *>
IO.println (toString e) *>
IO.println (repr "   aaa   ".trim) *>
showChars s₁.utf8ByteSize.toNat s₁ 0  *>
pure 0
