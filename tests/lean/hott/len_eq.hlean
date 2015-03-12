import init.axioms.ua
open nat unit equiv is_trunc

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n}, A → vector A n → vector A (succ n)

open vector
notation a :: b := cons a b

definition const {A : Type} : Π (n : nat), A → vector A n
| zero     a := nil
| (succ n) a := a :: const n a

definition head {A : Type} : Π {n : nat}, vector A (succ n) → A
| n (x :: xs) := x

theorem singlenton_vector_unit : ∀ {n : nat} (v w : vector unit n), v = w
| zero     nil        nil        := rfl
| (succ n) (star::xs) (star::ys) :=
  begin
    have h₁ : xs = ys, from singlenton_vector_unit xs ys,
    rewrite h₁
  end

private definition f (n m : nat) (v : vector unit n) : vector unit m := const m star

theorem vn_eqv_vm (n m : nat) : vector unit n ≃ vector unit m :=
equiv.MK (f n m) (f m n)
  (take v : vector unit m, singlenton_vector_unit (f n m (f m n v)) v)
  (take v : vector unit n, singlenton_vector_unit (f m n (f n m v)) v)

theorem vn_eq_vm (n m : nat) : vector unit n = vector unit m :=
ua (vn_eqv_vm n m)

definition vector_inj (A : Type) := ∀ (n m : nat), vector A n = vector A m → n = m

theorem not_vector_inj : ¬ vector_inj unit :=
assume H : vector_inj unit,
have aux₁ : 0 = 1, from H 0 1 (vn_eq_vm 0 1),
lift.down (nat.no_confusion aux₁)

definition cast {A B : Type} (H : A = B) (a : A) : B :=
eq.rec_on H a

open sigma

definition heq {A B : Type} (a : A) (b : B) :=
Σ (H : A = B), cast H a = b

infix `==`:50 := heq

definition heq.type_eq {A B : Type} {a : A} {b : B} : a == b → A = B
| ⟨H, e⟩ := H

definition heq.symm : ∀ {A B : Type} {a : A} {b : B}, a == b → b == a
| A A a a ⟨eq.refl A, eq.refl a⟩ :=  ⟨eq.refl A, eq.refl a⟩

definition heq.trans : ∀ {A B C : Type} {a : A} {b : B} {c : C}, a == b → b == c → a == c
| A A A a a a ⟨eq.refl A, eq.refl a⟩ ⟨eq.refl A, eq.refl a⟩ := ⟨eq.refl A, eq.refl a⟩

theorem cast_heq : ∀ {A B : Type} (H : A = B) (a : A), cast H a == a
| A A (eq.refl A) a := ⟨eq.refl A, eq.refl a⟩

definition default (A : Type) [H : inhabited A] : A :=
inhabited.rec_on H (λ a, a)

definition lem_eq (A : Type) : Type :=
∀ (n m : nat) (v : vector A n) (w : vector A m), v == w → n = m

theorem lem_eq_iff_vector_inj (A : Type) [inh : inhabited A] : lem_eq A ↔ vector_inj A :=
iff.intro
  (assume Hl : lem_eq A,
   assume n m he,
   assert a : A, from default A,
   assert v : vector A n, from const n a,
   have e₁  : v == cast he v, from heq.symm (cast_heq he v),
   Hl n m v (cast he v) e₁)
  (assume Hr : vector_inj A,
   assume n m v w he,
   Hr n m (heq.type_eq he))

theorem lem_eq_of_not_inhabited (A : Type) [ninh : inhabited A → empty] : lem_eq A :=
take (n m : nat),
match n with
| zero      :=
  match m with
  | zero      := take v w He, rfl
  | (succ m₁) :=
    take (v : vector A zero) (w : vector A (succ m₁)),
    empty.elim _ (ninh (inhabited.mk (head w)))
  end
| (succ n₁) :=
  take (v : vector A (succ n₁)) (w : vector A m),
  empty.elim _ (ninh (inhabited.mk (head v)))
end
