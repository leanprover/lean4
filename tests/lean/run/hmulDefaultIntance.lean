class HMul (α β : Type _) (γ : outParam (Type _)) where
  hmul : α → β → γ

@[defaultInstance]
instance [Mul α] : HMul α α α where
  hmul a b := a * b

infix:70 "*'" => HMul.hmul

instance : HMul Nat Bool Nat where
  hmul
    | x, true  => x
    | x, false => 0

#check 10 *' true

#check fun x => x *' 1
