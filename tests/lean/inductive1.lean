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
