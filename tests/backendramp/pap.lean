--  RUN: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET
--  RUN: ./validate-lean.sh %s 


-- | check that we generate pap and papExtend.
-- CHECK: lz.pap
-- CHECK: lz.papExtend

-- makeList: 
-- 1 2 3 4 5

-- INCREMENT: 
-- 2 3 4 5 6

-- 1 + 2 + 3 + 4 + 5 + 5 = 15 + 5 = 20
-- CHECK-INTERPRET: 20

set_option trace.compiler.ir.init true
inductive MyList
| Nil : MyList
| Cons : Nat -> MyList -> MyList

open MyList

instance : Inhabited MyList := ⟨Nil⟩


partial def makeList : Nat -> MyList
| 0 => Nil
| n => Cons n (makeList (n-1)) 

def mapList : (Nat -> Nat) -> MyList -> MyList
| _, Nil => Nil
| f, Cons x xs => Cons (f x) (mapList f xs)

def sumList : MyList -> Nat
| Nil => 0
| Cons x xs => x + (sumList xs)

def increment : Nat -> Nat
| x => x + 1



unsafe def main : List String → IO Unit
| _ => IO.println (sumList (mapList increment (makeList 5)))
