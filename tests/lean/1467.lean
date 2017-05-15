constants f g h : ℕ → ℕ
axiom H_f_g : ∀ n, f (g n) = n

example (m : ℕ) : h m = h m :=
begin
pose n : ℕ := g m,
note H : f n = m := begin dsimp, rw H_f_g end,
subst H, -- Error here
end

set_option pp.instantiate_mvars false

example (m : ℕ) : h m = h m :=
begin
define n : ℕ, -- add metavar
exact g m,
note H : f n = m := begin dsimp, rw H_f_g end,
subst H, -- Error here
end

example (m : ℕ) : h m = h m :=
begin
pose n : ℕ := g m,
note H : f n = m := begin dsimp, rw H_f_g end,
subst m, -- Error here
end

set_option pp.instantiate_mvars false

example (m : ℕ) : h m = h m :=
begin
define n : ℕ, -- add metavar
exact g m,
note H : f n = m := begin dsimp, rw H_f_g end,
subst m, -- Error here
end

example (m p: ℕ) : h m = h m :=
begin
pose a : ℕ := g p,
pose n : ℕ := g a,
clear p -- Error here
end
