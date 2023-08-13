namespace MkAndValAreOptimizedAway

structure MyZero where
  val : Nat

def MyZero.valImpl (_self : MyZero) : Nat := 0
attribute [implemented_by MyZero.valImpl] MyZero.val

unsafe def MyZero.mkImpl (_val : Nat) : MyZero := unsafeCast 0
attribute [implemented_by MyZero.mkImpl] MyZero.mk

#eval (MyZero.mk 1).val -- 1

end MkAndValAreOptimizedAway

namespace UsingAttr

@[opaque_repr]
structure MyZero where
  val : Nat

def MyZero.valImpl (_self : MyZero) : Nat := 0
attribute [implemented_by MyZero.valImpl] MyZero.val

unsafe def MyZero.mkImpl (_val : Nat) : MyZero := unsafeCast 0
attribute [implemented_by MyZero.mkImpl] MyZero.mk

#eval (MyZero.mk 1).val -- 0

-- FIXME: it would be nice if we didn't have to override casesOn too
@[inline] def MyZero.casesOnImpl {motive : MyZero → Sort u} (t : MyZero)
    (mk : ∀ val, motive { val }) : motive t := mk _
attribute [implemented_by MyZero.casesOnImpl] MyZero.casesOn

-- we need a blackBox here because the compiler will optimize
-- `(MyZero.mk n).casesOn f` to `f n` otherwise (and this is desirable, even for opaque_repr types)
@[noinline] def blackBox := @id
#eval ((blackBox (MyZero.mk 1)).casesOn fun n => n : Nat) -- 0

end UsingAttr
