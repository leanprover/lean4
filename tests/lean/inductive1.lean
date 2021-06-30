

-- Test1
inductive T1 : Nat -- Error, resultant type is not a sort


-- Test2
mutual

inductive T1 : Prop

inductive T2 : Type -- Error resulting universe mismatch

end

-- Test3
universe u v
mutual

inductive T1 (x : Nat) : Type u

inductive T2 (x : Nat) : Nat → Type v -- Error resulting universe mismatch

end

-- Test4
mutual

inductive T1 (b : Bool) (x : Nat)  : Type

inductive T2 (b : Bool) (x : Bool) : Type -- Type mismatch at 'x'

end

-- Test5
mutual

inductive T1 (b : Bool) (x : Nat)  : Type

inductive T2 (x : Bool) : Type -- number of parameters mismatch

end

-- Test6
mutual

inductive T1 (b : Bool) (x : Nat)  : Type

inductive T2 (b : Bool) {x : Nat} : Type -- binder annotation mismatch at 'x'

end


-- Test7
mutual

inductive T1.{w1} (b : Bool) (x : Nat) : Type

inductive T2.{w2} (b : Bool) (x : Nat) : Type -- universe parameter mismatch

end

-- Test8
namespace Boo

def T1.bla := 10

inductive T1 : Type
| bla : T1  -- Boo.T1.bla has already been defined

def T1 := 20

inductive T1 : Type -- Boo.T1 has already been defined
| bla : T1

end Boo

-- Test9

partial inductive T1 : Type -- invalid use of partial
noncomputable inductive T1 : Type -- invalid use of noncomputable
@[inline] inductive T1 : Type -- invalid use of attributes

private inductive T1 : Type
| private mk : T1 -- invalid private constructor in private inductive type


-- Test10
mutual

inductive T1 : Type

unsafe inductive T2 : Type

end

-- Test11
inductive T1 : Nat → Type
| z1 : T1 0
| z2 -- constructor resulting type must be specified in inductive family declaration


-- Test12
inductive T1 : Nat → Type
| z1 : T1 -- unexpected constructor resulting type

inductive T1 : Nat → Type
| z1 : Nat -- unexpected constructor resulting type


-- Test13

inductive A (α : Type u) (β : Type v)
| nil {}
| protected cons : α → β → A α β → A α β

open A
#check cons -- unknown `cons`, it is protected
