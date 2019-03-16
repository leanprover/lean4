def show_chars : nat → string → string.utf8_pos → io unit
| 0     _ _   := pure ()
| (n+1) s idx :=
  unless (s.utf8_at_end idx) $
    io.println (">> " ++ to_string (s.utf8_get idx)) *>
    show_chars n s (s.utf8_next idx)

def main : io uint32 :=
let s₁ := "hello α_world_β" in
let b  := string.utf8_begin in
let e  := s₁.utf8_byte_size in
io.println (s₁.extract b e) *>
io.println (s₁.extract (b+2) e) *>
io.println (s₁.extract (b+2) (e-1)) *>
io.println (s₁.extract (b+2) (e-2)) *>
io.println (s₁.extract (b+7) e) *>
io.println (s₁.extract (b+8) e) *>
io.println (to_string e) *>
io.println (repr "   aaa   ".trim) *>
show_chars s₁.utf8_byte_size.to_nat s₁ 0  *>
pure 0
