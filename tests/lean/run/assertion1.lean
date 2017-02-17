universe variables u v

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v)

universe variables u1 v1 u2 v2

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)

@[reducible] definition ProductCategory (C : Category) (D : Category) :
  Category :=
  {
    Obj      := C^.Obj × D^.Obj,
    Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd))
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

@[reducible] definition TensorProduct ( C: Category ) := Functor ( C × C ) C

structure MonoidalCategory
  extends carrier : Category :=
  (tensor : TensorProduct carrier)

instance MonoidalCategory_coercion : has_coe MonoidalCategory Category :=
  ⟨MonoidalCategory.to_Category⟩

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
@[reducible] definition MonoidalCategory.tensorObjects { C : MonoidalCategory } ( X Y : C^.Obj ) : C^.Obj := C^.tensor^.onObjects (X, Y)

definition tensor_on_left { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects Z X
}
