import macros
import subtype
using subtype

namespace num
theorem inhabited_ind : inhabited ind
-- We use as the witness for non-emptiness, the value w in ind that is not convered by f.
:= obtain f His, from infinity,
   obtain w Hw, from and_elimr His,
      inhabited_intro w

definition S := ε (inhabited_ex_intro infinity) (λ f, injective f ∧ non_surjective f)
definition Z := ε inhabited_ind (λ y, ∀ x, ¬ S x = y)

theorem injective_S      : injective S
:= and_eliml (exists_to_eps infinity)

theorem non_surjective_S : non_surjective S
:= and_elimr (exists_to_eps infinity)

theorem S_ne_Z (i : ind) : S i ≠ Z
:= obtain w Hw, from non_surjective_S,
     eps_ax inhabited_ind w Hw i

definition N (i : ind) : Bool
:= ∀ P, P Z → (∀ x, P x → P (S x)) → P i

theorem N_Z : N Z
:= λ P Hz Hi, Hz

theorem N_S {i : ind} (H : N i) : N (S i)
:= λ P Hz Hi, Hi i (H P Hz Hi)

theorem N_smallest : ∀ P : ind → Bool, P Z → (∀ x, P x → P (S x)) → (∀ i, N i → P i)
:= λ P Hz Hi i Hni, Hni P Hz Hi

definition num := subtype ind N

theorem inhab : inhabited num
:= subtype_inhabited (exists_intro Z N_Z)

definition zero : num
:= abst Z inhab

theorem zero_pred : N Z
:= N_Z

definition succ (n : num) : num
:= abst (S (rep n)) inhab

theorem succ_pred (n : num) : N (S (rep n))
:= have N_n : N (rep n),
     from P_rep n,
   show N (S (rep n)),
     from N_S N_n

theorem succ_inj (a b : num) : succ a = succ b → a = b
:= assume Heq1 : succ a = succ b,
   have Heq2 : S (rep a) = S (rep b),
      from abst_inj inhab (succ_pred a) (succ_pred b) Heq1,
   have rep_eq : (rep a) = (rep b),
      from injective_S (rep a) (rep b) Heq2,
   show a = b,
      from rep_inj rep_eq

theorem succ_nz (a : num) : succ a ≠ zero
:= assume R : succ a = zero,
   have Heq1 : S (rep a) = Z,
      from abst_inj inhab (succ_pred a) zero_pred R,
   show false,
      from absurd Heq1 (S_ne_Z (rep a))

theorem induction {P : num → Bool} (H1 : P zero) (H2 : ∀ n, P n → P (succ n)) : ∀ a, P a
:= take a,
   let Q := λ x, N x ∧ P (abst x inhab)
   in have QZ : Q Z,
        from and_intro zero_pred H1,
      have QS : ∀ x, Q x → Q (S x),
        from take x, assume Qx,
               have Hp1 : P (succ (abst x inhab)),
                 from H2 (abst x inhab) (and_elimr Qx),
               have Hp2 : P (abst (S (rep (abst x inhab))) inhab),
                 from Hp1,
               have Nx : N x,
                 from and_eliml Qx,
               have rep_eq : rep (abst x inhab) = x,
                 from rep_abst inhab x Nx,
               show Q (S x),
                 from and_intro (N_S Nx) (subst Hp2 rep_eq),
      have Qa : P (abst (rep a) inhab),
        from and_elimr (N_smallest Q QZ QS (rep a) (P_rep a)),
      have abst_eq : abst (rep a) inhab = a,
        from abst_rep inhab a,
      show P a,
        from subst Qa abst_eq

set_opaque num  true
set_opaque Z    true
set_opaque S    true
set_opaque zero true
set_opaque succ true
end

definition num := num::num
