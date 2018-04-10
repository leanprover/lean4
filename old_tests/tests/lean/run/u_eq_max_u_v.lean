universe variables u v u1 u2 v1 v2

set_option pp.universes true

open smt_tactic
meta def blast : tactic unit := using_smt $ intros >> add_lemmas_from_facts >> iterate_at_most 3 ematch
notation `♮` := by blast

structure semigroup_morphism { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) :=
  (map: α → β)
  (multiplicative : ∀ x y : α, map(x * y) = map(x) * map(y))

attribute [simp] semigroup_morphism.multiplicative

@[reducible] instance semigroup_morphism_to_map { α β : Type u } { s : semigroup α } { t: semigroup β } : has_coe_to_fun (semigroup_morphism s t) :=
{ F   := λ f, Π x : α, β,
  coe := semigroup_morphism.map }

@[reducible] definition semigroup_identity { α : Type u } ( s: semigroup α ) : semigroup_morphism s s := ⟨ id, ♮ ⟩

@[reducible] definition semigroup_morphism_composition
  { α β γ : Type u } { s: semigroup α } { t: semigroup β } { u: semigroup γ}
  ( f: semigroup_morphism s t ) ( g: semigroup_morphism t u ) : semigroup_morphism s u :=
{
  map := λ x, g (f x),
  multiplicative := begin intros, simp [coe_fn] end
}

local attribute [simp] mul_comm mul_assoc mul_left_comm

@[reducible] definition semigroup_product { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) : semigroup (α × β) := {
  mul := λ p q, (p^.fst * q^.fst, p^.snd * q^.snd),
  mul_assoc := begin
                intros,
                simp [@has_mul.mul (α × β)]
              end
}

definition semigroup_morphism_product
  { α β γ δ : Type u }
  { s_f : semigroup α } { s_g: semigroup β } { t_f : semigroup γ} { t_g: semigroup δ }
  ( f : semigroup_morphism s_f t_f ) ( g : semigroup_morphism s_g t_g )
  : semigroup_morphism (semigroup_product s_f s_g) (semigroup_product t_f t_g) := {
  map := λ p, (f p.1, g p.2),
  multiplicative :=
    begin
      -- cf https://groups.google.com/d/msg/lean-user/bVs5FdjClp4/tfHiVjLIBAAJ
      intros,
      unfold has_mul.mul,
      dsimp [coe_fn],
      simp
    end
}

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v)

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))

@[reducible] definition ProductCategory (C : Category) (D : Category) :
  Category :=
  {
    Obj      := C^.Obj × D^.Obj,
    Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd))
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

structure PreMonoidalCategory
  extends carrier : Category :=
  (tensor : Functor (carrier × carrier) carrier)

definition CategoryOfSemigroups : Category :=
{
    Obj := Σ α : Type u, semigroup α,
    Hom := λ s t, semigroup_morphism s.2 t.2
}

definition PreMonoidalCategoryOfSemigroups : PreMonoidalCategory := {
  CategoryOfSemigroups with
  tensor               := {
    onObjects   := λ p, sigma.mk (p.1.1 × p.2.1) (semigroup_product p.1.2 p.2.2),
    onMorphisms := λ s t f, semigroup_morphism_product f.1 f.2
  }
}
