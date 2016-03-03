--

open function

structure bijection (A : Type) :=
(func finv : A → A)
(linv : finv ∘ func = id)
(rinv : func ∘ finv = id)

attribute bijection.func [coercion]

namespace bijection
  variable {A : Type}

  definition comp (f g : bijection A) : bijection A :=
  bijection.mk
    (f ∘ g)
    (finv g ∘ finv f)
    (by rewrite [comp.assoc, -{finv f ∘ _}comp.assoc, linv f, comp.left_id, linv g])
    (by rewrite [-comp.assoc, {_ ∘ finv g}comp.assoc, rinv g, comp.right_id, rinv f])

  infixr ` ∘b `:100 := comp

  lemma compose.assoc (f g h : bijection A) : (f ∘b g) ∘b h = f ∘b (g ∘b h) := rfl

  definition id : bijection A :=
  bijection.mk id id (comp.left_id id) (comp.left_id id)

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
  bijection.rec_on f (λfunc finv linv rinv, by rewrite [↑inv, ↑comp, linv])
end bijection
