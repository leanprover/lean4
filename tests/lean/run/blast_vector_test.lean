import data.nat
open nat

lemma addl_eq_add [simp] (n m : nat) : (:n ⊕ m:) = n + m :=
!add_eq_addl

-- Casting notation
notation `⟨`:max a `⟩`:0 := cast (by inst_simp) a

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n}, A → vector A n → vector A (succ n)

namespace vector

notation a :: b := cons a b
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

variable {A : Type}

private definition append_aux : Π {n m : nat}, vector A n → vector A m → vector A (n ⊕ m)
| 0        m []     w := w
| (succ n) m (a::v) w := a :: (append_aux v w)

theorem append_aux_nil_left [simp] {n : nat} (v : vector A n) : append_aux [] v == v :=
!heq.refl

theorem append_aux_cons [simp] {n m : nat} (h : A) (t : vector A n) (v : vector A m) : append_aux (h::t) v ==  h :: (append_aux t v) :=
!heq.refl

definition append {n m : nat} (v : vector A n) (w : vector A m) : vector A (n + m) :=
⟨append_aux v w⟩

section

theorem append_nil_left [simp] {n : nat} (v : vector A n) : append [] v == v :=
by unfold append ; inst_simp

theorem append_cons [simp] {n m : nat} (h : A) (t : vector A n) (v : vector A m) : (: append (h::t) v :) == (: h::(append t v) :) :=
by unfold append ; inst_simp
end

theorem append_nil_right [simp] {n : nat} (v : vector A n) : append v [] == v :=
by rec_inst_simp

attribute succ_add [simp]

theorem append_assoc [simp] {n₁ n₂ n₃ : nat} (v₁ : vector A n₁) (v₂ : vector A n₂) (v₃ : vector A n₃) : append v₁ (append v₂ v₃) == append (append v₁ v₂) v₃ :=
by rec_inst_simp

definition concat : Π {n : nat}, vector A n → A → vector A (succ n)
| concat []     a := [a]
| concat (b::v) a := b :: concat v a

theorem concat_nil [simp] (a : A) : concat [] a = [a] :=
rfl

theorem concat_cons [simp] {n : nat} (b : A) (v : vector A n) (a : A) : concat (b :: v) a = b :: concat v a :=
rfl

definition reverse : Π {n : nat}, vector A n → vector A n
| 0     []        := []
| (n+1) (x :: xs) := concat (reverse xs) x

theorem reverse_nil [simp] : reverse [] = @nil A :=
rfl

theorem reverse_cons [simp] {n : nat} (a : A) (v : vector A n) : reverse (a::v) = concat (reverse v) a :=
rfl

theorem reverse_concat [simp] : ∀ {n : nat} (xs : vector A n) (a : A), reverse (concat xs a) = a :: reverse xs :=
by rec_inst_simp

theorem reverse_reverse [simp] : ∀ {n : nat} (xs : vector A n), reverse (reverse xs) = xs :=
by rec_inst_simp

theorem append_reverse_cons [simp] {n : nat} (v : vector A n) : ∀ (m : ℕ) (w : vector A m) (a : A),
  append v (reverse (cons a w)) == concat (append v (reverse w)) a :=
by induction v; inst_simp; inst_simp

theorem reverse_append [simp] : ∀ {n m : nat} (v : vector A n) (w : vector A m),
  reverse (append v w) == append (reverse w) (reverse v) :=
by rec_inst_simp

definition vplus : Π {n : ℕ} (v₁ v₂ : vector ℕ n), vector ℕ n
| nat.zero [] [] := []
| (nat.succ m) (x::xs) (y::ys) := (x + y) :: vplus xs ys

lemma vplus.def1 [simp] : vplus [] [] = @nil ℕ := rfl
lemma vplus.def2 [simp] {n : ℕ} (v₁ v₂ : vector ℕ n) (a₁ a₂ : ℕ) : (: vplus (a₁ :: v₁) (a₂ :: v₂) :) = (a₁ + a₂) :: vplus v₁ v₂ := rfl

lemma vplus_weird {n₁ n₂ : ℕ} (v₁ : vector ℕ n₁) (v₂ : vector ℕ n₂) (a b : ℕ) :
  vplus (a :: append v₁ v₂) ⟨b :: append v₂ v₁⟩ == (a + b) :: vplus (append v₁ v₂) ⟨append v₂ v₁⟩ :=
sorry -- TODO need to traverse equivalence class when matching against a meta-variable

end vector
