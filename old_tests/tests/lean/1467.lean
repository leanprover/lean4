constants f g h : ℕ → ℕ
axiom H_f_g : ∀ n, f (g n) = n

example (m : ℕ) : h m = h m :=
begin
let n : ℕ := g m,
have H : f n = m := begin rw H_f_g end,
subst H, -- Error here
end

set_option pp.instantiate_mvars false

example (m : ℕ) : h m = h m :=
begin
let n : ℕ, -- add metavar
exact g m,
have H : f n = m := begin rw H_f_g end,
subst H, -- Error here
end

example (m : ℕ) : h m = h m :=
begin
let n : ℕ := g m,
have H : f n = m := begin rw H_f_g end,
subst m, -- Error here
end

set_option pp.instantiate_mvars false

example (m : ℕ) : h m = h m :=
begin
let n : ℕ, -- add metavar
exact g m,
have H : f n = m := begin rw H_f_g end,
subst m, -- Error here
end

example (m p: ℕ) : h m = h m :=
begin
let a : ℕ := g p,
let n : ℕ := g a,
clear p -- Error here
end
