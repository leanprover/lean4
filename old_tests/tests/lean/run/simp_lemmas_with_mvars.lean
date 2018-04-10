lemma {u} if_pos' {c : Prop} [h : decidable c] (hc : c) {α : Sort u} (t e : α) : (ite c t e) = t :=
if_pos hc

example (a b : nat) (h : a = b) : (if a = b then 0 else 1) = cond (if a = b then tt else ff) 0 1 :=
begin
  simp only [if_pos' h, cond],
end

example (a b : nat) (h : a = b) : (if a = b then 0 else 1) = cond (if a = b then tt else ff) 0 1 :=
begin
  simp only [if_pos h, cond],
end

example (a b c : nat) : a + b + c = b + a + c :=
begin
  simp only [add_comm _ b]
end

example (a b c : nat) (h : c = 0) : a + b + 0 = b + a + c :=
begin
  simp only [add_comm _ b],
  guard_target b + a + 0 = b + a + c,
  rw h
end

example (a b c : nat) (h : c = 0) : 0 + (a + b) = b + a + c :=
begin
  simp only [add_comm _ c, add_comm a _],
  guard_target 0 + (b + a) = c + (b + a),
  rw h
end
