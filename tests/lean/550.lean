--

open function

structure bijection (A : Type) :=
(func finv : A → A)
(linv : finv ∘ func = id)
(rinv : func ∘ finv = id)

attribute bijection.func [coercion]

namespace bijection
  variable {A : Type}

  definition compose (f g : bijection A) : bijection A :=
  bijection.mk
    (f ∘ g)
    (finv g ∘ finv f)
    (by rewrite [compose.assoc, -{finv f ∘ _}compose.assoc, linv f, compose.left_id, linv g])
    (by rewrite [-compose.assoc, {_ ∘ finv g}compose.assoc, rinv g, compose.right_id, rinv f])

  infixr ` ∘b `:100 := compose

  lemma compose.assoc (f g h : bijection A) : (f ∘b g) ∘b h = f ∘b (g ∘b h) := rfl

  definition id : bijection A :=
  bijection.mk id id (compose.left_id id) (compose.left_id id)

  lemma id.left_id (f : bijection A) : id ∘b f = f :=
  bijection.rec_on f (λx x x x, rfl)

  lemma id.right_id (f : bijection A) : f ∘b id = f :=
  bijection.rec_on f (λx x x x, rfl)

  definition inv (f : bijection A) : bijection A :=
  bijection.mk
    (finv f)
    (func f)
    (rinv f)
    (linv f)

  lemma inv.linv (f : bijection A) : inv f ∘b f = id :=
  bijection.rec_on f (λfunc finv linv rinv, by rewrite [↑inv, ↑compose, linv])
end bijection
