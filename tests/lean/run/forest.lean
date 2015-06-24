import data.prod
open prod

inductive tree (A : Type) : Type :=
| node : A → forest A → tree A
with forest : Type :=
| nil  : forest A
| cons : tree A → forest A → forest A

namespace manual
definition tree.below.{l₁ l₂}
     (A : Type.{l₁})
     (C₁ : tree A → Type.{l₂})
     (C₂ : forest A → Type.{l₂})
     (t : tree A) : Type.{max 1 l₂} :=
  @tree.rec_on A
    (λ t : tree A,   Type.{max 1 l₂})
    (λ t : forest A, Type.{max 1 l₂})
    t
    (λ (a : A) (f : forest A) (r : Type.{max 1 l₂}), prod.{l₂ (max 1 l₂)} (C₂ f) r)
    poly_unit.{max 1 l₂}
    (λ (t : tree A) (f : forest A) (rt : Type.{max 1 l₂}) (rf : Type.{max 1 l₂}),
        prod.{(max 1 l₂) (max 1 l₂)} (prod.{l₂ (max 1 l₂)} (C₁ t) rt) (prod.{l₂ (max 1 l₂)} (C₂ f) rf))

definition forest.below.{l₁ l₂}
     (A : Type.{l₁})
     (C₁ : tree A → Type.{l₂})
     (C₂ : forest A → Type.{l₂})
     (f : forest A) : Type.{max 1 l₂} :=
  @forest.rec_on A
    (λ t : tree A,   Type.{max 1 l₂})
    (λ t : forest A, Type.{max 1 l₂})
    f
    (λ (a : A) (f : forest A) (r : Type.{max 1 l₂}), prod.{l₂ (max 1 l₂)} (C₂ f) r)
    poly_unit.{max 1 l₂}
    (λ (t : tree A) (f : forest A) (rt : Type.{max 1 l₂}) (rf : Type.{max 1 l₂}),
        prod.{(max 1 l₂) (max 1 l₂)} (prod.{l₂ (max 1 l₂)} (C₁ t) rt) (prod.{l₂ (max 1 l₂)} (C₂ f) rf))

definition tree.brec_on.{l₁ l₂}
     (A  : Type.{l₁})
     (C₁ : tree A → Type.{l₂})
     (C₂ : forest A → Type.{l₂})
     (t  : tree A)
     (F₁ : Π (t : tree A),   tree.below A C₁ C₂ t   → C₁ t)
     (F₂ : Π (f : forest A), forest.below A C₁ C₂ f → C₂ f)
  : C₁ t :=
have general : prod.{l₂ (max 1 l₂)} (C₁ t) (tree.below A C₁ C₂ t), from
  @tree.rec_on
    A
    (λ (t' : tree A),   prod.{l₂ (max 1 l₂)} (C₁ t') (tree.below A C₁ C₂ t'))
    (λ (f' : forest A), prod.{l₂ (max 1 l₂)} (C₂ f') (forest.below A C₁ C₂ f'))
    t
    (λ (a : A) (f : forest A) (r : prod.{l₂ (max 1 l₂)} (C₂ f) (forest.below A C₁ C₂ f)),
       have b : tree.below A C₁ C₂ (tree.node a f), from
         r,
       have c : C₁ (tree.node a f), from
         F₁ (tree.node a f) b,
       prod.mk.{l₂ (max 1 l₂)} c b)
    (have b : forest.below A C₁ C₂ (forest.nil A), from
      poly_unit.star.{max 1 l₂},
     have c : C₂ (forest.nil A), from
      F₂ (forest.nil A) b,
     prod.mk.{l₂ (max 1 l₂)} c b)
    (λ (t : tree A)
       (f : forest A)
       (rt : prod.{l₂ (max 1 l₂)} (C₁ t) (tree.below A C₁ C₂ t))
       (rf : prod.{l₂ (max 1 l₂)} (C₂ f) (forest.below A C₁ C₂ f)),
     have b : forest.below A C₁ C₂ (forest.cons t f), from
       prod.mk.{(max 1 l₂) (max 1 l₂)} rt rf,
     have c : C₂ (forest.cons t f), from
       F₂ (forest.cons t f) b,
     prod.mk.{l₂ (max 1 l₂)} c b),
pr₁ general

definition forest.brec_on.{l₁ l₂}
     (A  : Type.{l₁})
     (C₁ : tree A → Type.{l₂})
     (C₂ : forest A → Type.{l₂})
     (f  : forest A)
     (F₁ : Π (t : tree A),   tree.below A C₁ C₂ t   → C₁ t)
     (F₂ : Π (f : forest A), forest.below A C₁ C₂ f → C₂ f)
  : C₂ f :=
have general : prod.{l₂ (max 1 l₂)} (C₂ f) (forest.below A C₁ C₂ f), from
  @forest.rec_on
    A
    (λ (t' : tree A),   prod.{l₂ (max 1 l₂)} (C₁ t') (tree.below A C₁ C₂ t'))
    (λ (f' : forest A), prod.{l₂ (max 1 l₂)} (C₂ f') (forest.below A C₁ C₂ f'))
    f
    (λ (a : A) (f : forest A) (r : prod.{l₂ (max 1 l₂)} (C₂ f) (forest.below A C₁ C₂ f)),
       have b : tree.below A C₁ C₂ (tree.node a f), from
         r,
       have c : C₁ (tree.node a f), from
         F₁ (tree.node a f) b,
       prod.mk.{l₂ (max 1 l₂)} c b)
    (have b : forest.below A C₁ C₂ (forest.nil A), from
      poly_unit.star.{max 1 l₂},
     have c : C₂ (forest.nil A), from
      F₂ (forest.nil A) b,
     prod.mk.{l₂ (max 1 l₂)} c b)
    (λ (t : tree A)
       (f : forest A)
       (rt : prod.{l₂ (max 1 l₂)} (C₁ t) (tree.below A C₁ C₂ t))
       (rf : prod.{l₂ (max 1 l₂)} (C₂ f) (forest.below A C₁ C₂ f)),
     have b : forest.below A C₁ C₂ (forest.cons t f), from
       prod.mk.{(max 1 l₂) (max 1 l₂)} rt rf,
     have c : C₂ (forest.cons t f), from
       F₂ (forest.cons t f) b,
     prod.mk.{l₂ (max 1 l₂)} c b),
pr₁ general
end manual
