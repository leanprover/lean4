-- The type of h depends on the zeta-expansion of n.  When we abstract the
-- subterm proving `n < 5`, we need to zeta-expand n not just in the subterm,
-- but also in the local context.

lemma bug₁ : fin 5 :=
let n : ℕ := 3 in
have h : n < 5, from dec_trivial,
⟨n, by abstract { exact h }⟩

def bug₂ : fin 5 :=
let n : ℕ := 3 in
have h : n < 5, from dec_trivial,
⟨n, show n < 5, from h⟩
 -- ^^^^ the show is only used to trigger automatic abstraction
