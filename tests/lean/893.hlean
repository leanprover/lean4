example {A : Type} (f : A → A) (a : A) (H : f a = a) : unit :=
begin
  induction H, -- this should raise an error
  exact unit.star
end
