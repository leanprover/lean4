class Funny (F : Type _) (A B : outParam (Type _)) where
  toFun : F → A → B

instance [Funny F A B] : CoeFun F fun _ => A → B where coe := Funny.toFun

class MulHomClass (F) (A B : outParam _) [Mul A] [Mul B] extends Funny F A B
class Monoid (M) extends Mul M
instance [Mul A] : Mul (Id A) := ‹_›

#check Funny.toFun
#check MulHomClass.toFunny

example [Monoid A] [Monoid B] [MulHomClass F A B] : Funny F A B :=
  inferInstance

-- set_option trace.Meta.synthInstance true
example [Monoid A] [Monoid B] [MulHomClass F A B] (f : F) (a : A) : f a = f a := rfl -- infinite loop
