def show_chars : nat → string → string.utf8_pos → io unit
| 0     _ _   := pure ()
| (n+1) s idx :=
  unless (s.utf8_at_end idx) $
    io.println' (">> " ++ to_string (s.utf8_get idx)) *>
    show_chars n s (s.utf8_next idx)

def main : io uint32 :=
let s₁ := "hello α world β" in
io.println' (to_string s₁.utf8_byte_size) *>
show_chars s₁.utf8_byte_size.to_nat s₁ 0  *>
pure 0
