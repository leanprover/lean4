new_frontend

-- Test1
inductive T1 : Nat -- Error, resultant type is not a sort


-- Test2
mutual

inductive T1 : Prop

inductive T2 : Type -- Error resulting universe mismatch

end

-- Test3
universes u v
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

partial inductive T1 : Type -- invalid use of partial
