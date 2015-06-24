import data.prod

inductive ftree (A : Type) (B : Type) : Type :=
| leafa : ftree A B
| node  : (A → B → ftree A B) → (B → ftree A B) → ftree A B

set_option pp.universes true
check @ftree

namespace ftree

namespace manual
definition below.{l l₁ l₂} {A : Type.{l₁}} {B : Type.{l₂}} (C : ftree A B → Type.{l+1}) (t : ftree A B)
           : Type.{max l₁ l₂ (l+1)} :=
@ftree.rec.{(max l₁ l₂ (l+1))+1 l₁ l₂}
  A
  B
  (λ t : ftree A B,  Type.{max l₁ l₂ (l+1)})
  poly_unit.{max l₁ l₂ (l+1)}
  (λ (f₁ : A → B → ftree A B)
     (f₂ : B → ftree A B)
     (r₁ : Π (a : A) (b : B), Type.{max l₁ l₂ (l+1)})
     (r₂ : Π (b : B),         Type.{max l₁ l₂ (l+1)}),
     let fc₁ : Type.{max l₁ l₂ (l+1)} := Π (a : A) (b : B), C (f₁ a b) in
     let fc₂ : Type.{max l₂ l+1}      := Π (b : B), C (f₂ b) in
     let fr₁ : Type.{max l₁ l₂ (l+1)} := Π (a : A) (b : B), r₁ a b in
     let fr₂ : Type.{max l₁ l₂ (l+1)} := Π (b : B), r₂ b in
     let p₁  : Type.{max l₁ l₂ (l+1)} := prod.{(max l₁ l₂ (l+1)) (max l₁ l₂ (l+1))} fc₁ fr₁ in
     let p₂  : Type.{max l₁ l₂ (l+1)} := prod.{(max l₂ (l+1)) (max l₁ l₂ (l+1))} fc₂ fr₂ in
     prod.{(max l₁ l₂ (l+1)) (max l₁ l₂ (l+1))} p₁ p₂)
  t

definition pbelow.{l₁ l₂} {A : Type.{l₁}} {B : Type.{l₂}} (C : ftree A B → Prop) (t : ftree A B)
           : Prop :=
@ftree.rec.{1 l₁ l₂}
  A
  B
  (λ t : ftree A B,  Prop)
  true
  (λ (f₁ : A → B → ftree A B)
     (f₂ : B → ftree A B)
     (r₁ : Π (a : A) (b : B), Prop)
     (r₂ : Π (b : B),         Prop),
     let fc₁ : Prop := ∀ (a : A) (b : B), C (f₁ a b) in
     let fc₂ : Prop := ∀ (b : B), C (f₂ b) in
     let fr₁ : Prop := ∀ (a : A) (b : B), r₁ a b in
     let fr₂ : Prop := ∀ (b : B), r₂ b in
     let p₁  : Prop := fc₁ ∧ fr₁ in
     let p₂  : Prop := fc₂ ∧ fr₂ in
     p₁ ∧ p₂)
  t

definition brec_on.{l l₁ l₂} {A : Type.{l₁}} {B : Type.{l₂}} {C : ftree A B → Type.{l+1}}
                  (t : ftree A B)
                  (F : Π (t : ftree A B), @below A B C t → C t)
              : C t :=
have gen : prod.{(l+1) (max l₁ l₂ (l+1))} (C t) (@below A B C t), from
  @ftree.rec.{(max l₁ l₂ (l+1)) l₁ l₂}
    A
    B
    (λ t : ftree A B, prod.{(l+1) (max l₁ l₂ (l+1))} (C t) (@below A B C t))
    (have b : @below A B C (leafa A B), from
       poly_unit.star.{max l₁ l₂ (l+1)},
     have c : C (leafa A B), from
       F (leafa A B) b,
     prod.mk.{(l+1) (max l₁ l₂ (l+1))} c b)
    (λ (f₁ : A → B → ftree A B)
       (f₂ : B → ftree A B)
       (r₁ : Π (a : A) (b : B), prod.{(l+1) (max l₁ l₂ (l+1))} (C (f₁ a b)) (@below A B C (f₁ a b)))
       (r₂ : Π (b : B), prod.{(l+1) (max l₁ l₂ (l+1))} (C (f₂ b)) (@below A B C (f₂ b))),
       let fc₁ : Π (a : A) (b : B), C (f₁ a b)       := λ (a : A) (b : B), prod.pr1 (r₁ a b) in
       let fr₁ : Π (a : A) (b : B), @below A B C (f₁ a b) := λ (a : A) (b : B), prod.pr2 (r₁ a b) in
       let fc₂ : Π (b : B), C (f₂ b)                 := λ (b : B), prod.pr1 (r₂ b) in
       let fr₂ : Π (b : B), @below A B C (f₂ b)           := λ (b : B), prod.pr2 (r₂ b) in
       have b : @below A B C (node f₁ f₂), from
         prod.mk (prod.mk fc₁ fr₁) (prod.mk fc₂ fr₂),
       have c : C (node f₁ f₂), from
         F (node f₁ f₂) b,
       prod.mk c b)
    t,
prod.pr1 gen

definition binduction_on.{l₁ l₂} {A : Type.{l₁}} {B : Type.{l₂}} {C : ftree A B → Prop}
               (t : ftree A B)
               (F : Π (t : ftree A B), @ftree.ibelow A B C t → C t)
            : C t :=
have gen : C t ∧ @ftree.ibelow A B C t, from
  @ftree.rec.{0 l₁ l₂}
    A
    B
    (λ t : ftree A B, C t ∧ @ftree.ibelow A B C t)
    (have b : @ftree.ibelow A B C (leafa A B), from
       true.intro,
     have c : C (leafa A B), from
       F (leafa A B) b,
     and.intro c b)
    (λ (f₁ : A → B → ftree A B)
       (f₂ : B → ftree A B)
       (r₁ : ∀ (a : A) (b : B), C (f₁ a b) ∧ @ftree.ibelow A B C (f₁ a b))
       (r₂ : ∀ (b : B), C (f₂ b) ∧ @ftree.ibelow A B C (f₂ b)),
       let fc₁ : ∀ (a : A) (b : B), C (f₁ a b)        := λ (a : A) (b : B), and.elim_left  (r₁ a b) in
       let fr₁ : ∀ (a : A) (b : B), @ftree.ibelow A B C (f₁ a b) := λ (a : A) (b : B), and.elim_right (r₁ a b) in
       let fc₂ : ∀ (b : B), C (f₂ b)                  := λ (b : B), and.elim_left  (r₂ b) in
       let fr₂ : ∀ (b : B), @ftree.ibelow A B C (f₂ b)           := λ (b : B), and.elim_right (r₂ b) in
       have b : @ftree.ibelow A B C (node f₁ f₂), from
         and.intro (and.intro fc₁ fr₁) (and.intro fc₂ fr₂),
       have c : C (node f₁ f₂), from
         F (node f₁ f₂) b,
       and.intro c b)
    t,
and.elim_left gen
end manual
end ftree
