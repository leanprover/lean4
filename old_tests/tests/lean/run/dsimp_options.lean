example (b c : nat) : c = @bool.cases_on (λ _, nat) tt b c  :=
begin
  fail_if_success {dsimp {iota := ff}},
  dsimp {iota := tt},
  guard_target c = c,
  reflexivity
end

example (b c : nat) : c = @bool.cases_on (λ _, nat) tt b c  :=
begin
  dsimp, -- iota is tt by default
  guard_target c = c,
  reflexivity
end

example (b c : nat) : c = (λ x : nat, x) c  :=
begin
  fail_if_success {dsimp {beta := ff}},
  dsimp {beta := tt},
  guard_target c = c,
  reflexivity
end

example (b c : nat) : c = (λ x : nat, x) c  :=
begin
  dsimp, -- beta is tt by default
  guard_target c = c,
  reflexivity
end

example (b c : nat) : c = (b, c).2  :=
begin
  fail_if_success {dsimp {proj := ff}},
  dsimp {proj := tt},
  guard_target c = c,
  reflexivity
end

example (b c : nat) : c = (b, c).2  :=
begin
  dsimp, -- projection reduction is true by default IF argument is a constructor
  guard_target c = c,
  reflexivity
end

example (f g : nat → nat) : f ∘ g = λ x, f (g x) :=
begin
  fail_if_success {dsimp}, -- reducible definition (e.g., function.comp) are not unfolded by default
  dsimp [(∘)],
  guard_target (λ x, f (g x)) = λ x, f (g x),
  reflexivity
end

example (f g : nat → nat) : f ∘ g = λ x, f (g x) :=
begin
  dsimp [function.comp],
  guard_target (λ x, f (g x)) = λ x, f (g x),
  reflexivity
end

example (a : nat) : (let x := a in x) = a :=
begin
  fail_if_success{dsimp {zeta := ff}},
  dsimp {zeta := tt},
  guard_target a = a,
  reflexivity
end

example (a : nat) : (let x := a in x) = a :=
begin
  dsimp, -- zeta is tt by default
  guard_target a = a,
  reflexivity
end

example (a b : nat) : a + b = b + a :=
begin
  fail_if_success{dsimp}, -- will not unfold has_add.add applications
  apply add_comm
end
