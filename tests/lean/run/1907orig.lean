class MulOneClass (M : Type u) extends One M, Mul M

class FunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  coe : F → ∀ a : α, β a

instance (priority := 100) [FunLike F α β] : CoeFun F fun _ => ∀ a : α, β a where coe := FunLike.coe

section One

variable [One M] [One N]

structure OneHom (M : Type _) (N : Type _) [One M] [One N] where
  toFun : M → N
  map_one' : toFun 1 = 1

class OneHomClass (F : Type _) (M N : outParam (Type _)) [outParam (One M)] [outParam (One N)]
  extends FunLike F M fun _ => N where
  map_one : ∀ f : F, f 1 = 1

@[simp]
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 :=
  OneHomClass.map_one f

end One

section Mul

variable [Mul M] [Mul N]

structure MulHom (M : Type _) (N : Type _) [Mul M] [Mul N] where
  toFun : M → N
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

infixr:25 " →ₙ* " => MulHom

class MulHomClass (F : Type _) (M N : outParam (Type _)) [outParam (Mul M)] [outParam (Mul N)]
  extends FunLike F M fun _ => N where
  map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y

@[simp]
theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y :=
  MulHomClass.map_mul f x y

end Mul

section mul_one

variable [MulOneClass M] [MulOneClass N]

structure MonoidHom (M : Type _) (N : Type _) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N

infixr:25 " →* " => MonoidHom

class MonoidHomClass (F : Type _) (M N : outParam (Type _)) [outParam (MulOneClass M)]
   [outParam (MulOneClass N)] extends MulHomClass F M N, OneHomClass F M N

instance [MonoidHomClass F M N] : CoeTC F (M →* N) :=
  ⟨fun f => { toFun := f, map_one' := map_one f, map_mul' := map_mul f }⟩

-- Now we reverse the order of the parents in the extends clause:
class MonoidHomClass' (F : Type _) (M N : outParam (Type _)) [outParam (MulOneClass M)]
   [outParam (MulOneClass N)] extends OneHomClass F M N, MulHomClass F M N

instance [MonoidHomClass' F M N] : CoeTC F (M →* N) :=
  ⟨fun f => { toFun := f, map_one' := map_one f, map_mul' := map_mul f }⟩
