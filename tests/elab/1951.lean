class FunLike (F : Type _) (A : outParam (Type _)) (B : outParam (A → Type _)) where toFun : F → ∀ a, B a
instance [FunLike F A B] : CoeFun F fun _ => ∀ a, B a where coe := FunLike.toFun
class OneHomClass (F) (A B : outParam _) [One A] [One B] extends FunLike F A fun _ => B where
  map_one (f : F) : f 1 = 1
class MulHomClass (F) (A B : outParam _) [Mul A] [Mul B] extends FunLike F A fun _ => B
class Monoid (M) extends Mul M, One M
class MonoidHomClass (F) (A B : outParam _) [Monoid A] [Monoid B] extends MulHomClass F A B, OneHomClass F A B

theorem map_one [Monoid A] [Monoid B] [OneHomClass F A B] (f : F) : f 1 = 1 := OneHomClass.map_one f
example [Monoid M] [Monoid N] [MonoidHomClass F M N] (f : F) : f 1 = 1 := by
  simp only [map_one]
