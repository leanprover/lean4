import Lean

structure WrappedNat where
  val : Nat

structure WrappedFun (α) where
  fn : Nat → α

structure WrappedType where
  typ : Type

attribute [coe] WrappedNat.val
instance : Coe WrappedNat Nat where coe := WrappedNat.val

#eval Lean.Meta.registerCoercion ``WrappedFun.fn (some ⟨2, 1, .coeFun⟩)
instance : CoeFun (WrappedFun α) (fun _ => Nat → α) where coe := WrappedFun.fn

#eval Lean.Meta.registerCoercion ``WrappedType.typ (some ⟨1, 0, .coeSort⟩)
instance : CoeSort WrappedType Type where coe := WrappedType.typ

section coe
variable (n : WrappedNat)

#check (↑n : Nat)

#check n.val

end coe

section coeFun
variable (f : WrappedFun Nat) (g : Nat → WrappedFun Nat) (h : WrappedFun (WrappedFun Nat))

#check f.fn

#check ⇑f

#check ⇑f 1

#check ⇑(g 1)

#check g 1 2

#check ⇑h

end coeFun

section coeSort
variable (t : WrappedType)

#check t.typ
#check ↥t

end coeSort
