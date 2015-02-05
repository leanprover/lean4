import data.nat
open nat
constant f : nat → nat

theorem tst1 (x y : nat) (H1 : (λ z, z + 0) x = y) (H2 : x = y + 0) (H3 : x = y * 0) : f x = f y :=
begin
  rewrite [▸ x = y at (H1, H2), H2]
end
