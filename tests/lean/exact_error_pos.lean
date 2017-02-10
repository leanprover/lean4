constant f : nat → nat → nat


def ex1 : nat :=
begin
  exact 10 +
        (f 1 (f 0 tt))

end


def ex₂ : nat :=
begin
  apply 10 +
        (f 1 (f 0 tt))
end
