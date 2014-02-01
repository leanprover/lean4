import macros

definition injective {A B : (Type U)} (f : A → B)  := ∀ x1 x2, f x1 = f x2 → x1 = x2
definition non_surjective {A B : (Type U)} (f : A → B) := ∃ y, ∀ x, ¬ f x = y

-- The set of individuals
variable ind : Type
-- ind is infinite, i.e., there is a function f s.t. f is injective, and not surjective
axiom infinity : ∃ f : ind → ind, injective f ∧ non_surjective f

theorem nonempty_ind : nonempty ind
-- We use as the witness for non-emptiness, the value w in ind that is not convered by f.
:= obtain f His, from infinity,
   obtain w Hw, from and_elimr His,
      nonempty_intro w

definition S := ε (nonempty_ex_intro infinity) (λ f, injective f ∧ non_surjective f)
definition Z := ε nonempty_ind (λ y, ∀ x, ¬ S x = y)

theorem injective_S      : injective S
:= and_eliml (exists_to_eps infinity)

theorem non_surjective_S : non_surjective S
:= and_elimr (exists_to_eps infinity)

theorem S_ne_Z (i : ind) : S i ≠ Z
:= obtain w Hw, from non_surjective_S,
     eps_ax nonempty_ind w Hw i

definition N (i : ind) : Bool
:= ∀ P, P Z → (∀ x, P x → P (S x)) → P i

theorem N_Z : N Z
:= λ P Hz Hi, Hz

theorem N_S (i : ind) (H : N i) : N (S i)
:= λ P Hz Hi, Hi i (H P Hz Hi)

theorem N_smallest : ∀ P : ind → Bool, P Z → (∀ x, P x → P (S x)) → (∀ i, N i → P i)
:= λ P Hz Hi i Hni, Hni P Hz Hi

