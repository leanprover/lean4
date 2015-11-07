section
variables p : nat → Prop
variables q : nat → nat → Prop
variables f : Π (x y : nat), p x → q x y → nat
end


section
variables p : nat → Prop
variables q : Π (n m : nat), p n → p m → Prop
variables r : Π (n m : nat) (H₁ : p n) (H₂ : p m), q n m H₁ H₂ → Prop
variables h : Π (n m : nat)
                (H₁ : p n) (H₂ : p m) (H₃ : q n n H₁ H₁) (H₄ : q n m H₁ H₂)
                (H₅ : r n m H₁ H₂ H₄) (H₆ : r n n H₁ H₁ H₃), nat


definition h_congr (n₁ n₂ : nat) (e₁ : n₁ = n₂) (m₁ m₂ : nat) (e₂ : m₁ = m₂)
                   (H₁ : p n₁) (H₂ : p m₁)
                   (H₃ : q n₁ n₁ H₁ H₁)
                   (H₄ : q n₁ m₁ H₁ H₂)
                   (H₅ : r n₁ m₁ H₁ H₂ H₄)
                   (H₆ : r n₁ n₁ H₁ H₁ H₃) :
  h n₁ m₁ H₁ H₂ H₃ H₄ H₅ H₆ =
  h n₂ m₂ (eq.drec_on e₁ H₁)
          (eq.drec_on e₂ H₂)
          (eq.drec_on e₁ H₃)
          (eq.drec_on e₁ (eq.drec_on e₂ H₄))
          (eq.drec_on e₁ (eq.drec_on e₂ H₅))
          (eq.drec_on e₁ H₆) :=
begin
  apply eq.drec_on e₁,
  apply eq.drec_on e₂,
  apply rfl
end

-- set_option pp.implicit true
-- print h_congr
#congr h

exit

eq.drec_on e₁ (eq.drec_on e₂ (eq.refl (h n₂ m₂ (eq.rec_on e₁ H₁) (eq.rec_on e₂ H₂) (eq.drec_on e₁ H₃)
          (eq.drec_on e₁ (eq.drec_on e₂ H₄))
          (eq.drec_on e₁ (eq.drec_on e₂ H₅))
          (eq.drec_on e₁ H₆))))

sorry

exit



q x₁ H₁) :
              h x₁ H₁ H₂ = h x₂ (eq.rec_on e H₁) (eq.drec_on e H₂) :=
eq.drec_on e (eq.refl (h x₁ (eq.rec_on (eq.refl x₁) H₁) (eq.drec_on (eq.refl x₁) H₂)))

exit

variables h₂ : Π (n : nat) (H₁ : p n) (H₂ : q n H₁) (H₃ : r n H₁ H₂), nat

definition h_congr (x₁ x₂ : nat) (e : x₁ = x₂) (H₁ : p x₁) (H₂ : q x₁ H₁) :
              h x₁ H₁ H₂ = h x₂ (eq.rec_on e H₁) (eq.drec_on e H₂) :=
eq.drec_on e (eq.refl (h x₁ (eq.rec_on (eq.refl x₁) H₁) (eq.drec_on (eq.refl x₁) H₂)))

definition h_congr₂ (x₁ x₂ : nat) (e : x₁ = x₂) (H₁ : p x₁) (H₂ : q x₁ H₁) (H₃ : r x₁ H₁ H₂) :
              h₂ x₁ H₁ H₂ H₃ = h₂ x₂ (eq.rec_on e H₁) (eq.drec_on e H₂) (eq.drec_on e H₃) :=
eq.drec_on e (eq.refl (h₂ x₁ (eq.rec_on (eq.refl x₁) H₁) (eq.drec_on (eq.refl x₁) H₂) (eq.drec_on (eq.refl x₁) H₃)))


definition h_congr₃ (x₁ x₂ : nat) (e : x₁ = x₂) (H₁ : p x₁) (H₂ : q x₁ H₁) (H₃ : r x₁ H₁ H₂) :
              h₂ x₁ H₁ H₂ H₃ = h₂ x₂ (eq.rec_on e H₁) (eq.drec_on e H₂) (eq.drec_on e H₃) :=
begin
  congruence,
  apply e
end


-- print h_congr₃

-- exit

set_option pp.all true
print h_congr₂


#congr h

exit

set_option pp.all true
print h_congr

#congr h
end




exit
variables g : Π (A : Type) (x y : A) (B : Type) (z : B), x = y → y == z → nat

#congr g


exit



lemma f_congr
  (x₁ x₂ : nat) (e₁ : x₁ = x₂)
  (y₁ y₂ : nat) (e₂ : y₁ = y₂)
  (H₁ : p x₁)
  (H₂ : q x₁ y₁) :
  f x₁ y₁ H₁ H₂ =
  f x₂ y₂ (@eq.rec_on nat x₁ (λ (a : ℕ), p a) x₂ e₁ H₁)
          (@eq.rec_on nat x₁ (λ (a : ℕ), q a y₂) x₂ e₁ (@eq.rec_on nat y₁ (λ (a : ℕ), q x₁ a) y₂ e₂ H₂)) :=
let R := (eq.refl (f x₁ y₁ (@eq.rec_on nat x₁ (λ (a : ℕ), p a) x₁ (eq.refl x₁) H₁) (@eq.rec_on nat x₁ (λ (a : ℕ), q a y₁) x₁ (eq.refl x₁) (@eq.rec_on nat y₁ (λ (a : ℕ), q x₁ a) y₁ (eq.refl y₁) H₂)))) in
@eq.drec_on nat x₁
  (λ (z : ℕ) (H : x₁ = z),
     f x₁ y₁ H₁ H₂ =
     f z  y₂ (@eq.rec_on nat x₁ (λ a, p a) z H H₁)
             (@eq.rec_on nat x₁ (λ a, q a y₂) z H (@eq.rec_on nat y₁ (λ a, q x₁ a) y₂ e₂ H₂)))
  x₂ e₁
    (@eq.drec_on nat y₁
    (λ (z : ℕ) (H : y₁ = z),
      f x₁ y₁ H₁ H₂ =
      f x₁ z (@eq.rec_on nat x₁ (λ a, p a) x₁ (eq.refl x₁) H₁)
             (@eq.rec_on nat x₁ (λ a, q a z) x₁ (eq.refl x₁) (@eq.rec_on nat y₁ (λ a, q x₁ a) z H H₂)))
    y₂ e₂ R)



/-

     f x₁ y₁ H₁ H₂ =
     f x₁ y₂ (@eq.rec_on nat x₁ (λ a, p a) x₁ (eq.refl x₁) H₁)
             (@eq.rec_on nat x₁ (λ a, q a y₂) x₁ (eq.refl x₁) (@eq.rec_on nat y₁ (λ a, q x₁ a) y₂ e₂ H₂)))

-/
