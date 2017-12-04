example : (λ x y : nat, x + y) = (λ x y : nat, y + x) :=
begin
  funext,
  apply add_comm x y
end

example : (λ x y : nat, x + y) = (λ x y : nat, y + x) :=
begin
  funext z w,
  apply add_comm z w
end

example : (λ x y : nat, x + y) = (λ x y : nat, y + x) :=
begin
  funext z,
  funext w,
  apply add_comm z w
end

example : (λ x y : nat, x + y) = (λ x y : nat, y + x) :=
begin
  funext _,
  funext _,
  apply add_comm x y
end

example : (λ x y : nat, x + y) = (λ x y : nat, y + x) :=
begin
  funext _ _,
  apply add_comm x y
end

example : (λ x y : nat, x + 0) = (λ x y : nat, 0 + x) :=
begin
  funext _ _,
  apply add_comm x 0
end

example : (λ x y : nat, x + 0) = (λ x y : nat, 0 + x) :=
begin
  funext z _,
  apply add_comm z 0
end

example : (λ x y : nat, x + 0) = (λ x y : nat, 0 + x) :=
begin
  funext _ z,
  apply add_comm x 0
end

example : (λ x y : nat, x + 0) = (λ x y : nat, 0 + x) :=
begin
  funext z,
  funext _,
  apply add_comm z 0
end
