import data.nat
open nat algebra

set_option rewriter.syntactic true

example (x : nat) (H1 : x = 0) : x + 0 + 0 = 0 :=
begin
  rewrite *add_zero,
  rewrite H1
end
