#check "hello"

#check 1

#check fun (x : Nat) => x + 1

#eval (fun (x : Nat) => x + 1) 3

-- Recursive functions

def fact : Nat → Nat
| 0   => 1
| n+1 => (n+1) * fact n

#eval fact 4
#eval fact 20

-- Dot notation

#eval List.map (fun x => toString x) [1, 2, 3]

#check @toString

#eval [1, 2, 3].map fun x => toString x

def List.len1 {α} (xs : List α) : Nat :=
xs.length + 1

#eval [1, 2, 3].len1

-- Inductive datatypes

inductive Tree (α : Type)
| leaf : α → Tree
| node : Tree → Tree → Tree

namespace Tree

private def toStr {α} [ToString α] : Tree α → String
| leaf a          => toString a
| node left right => "(node " ++ toStr left ++ " " ++ toStr right ++ ")"

instance {α} [ToString α] : ToString (Tree α) := ⟨toStr⟩

end Tree

#eval toString (Tree.node (Tree.leaf 10) (Tree.leaf 20))

open Tree

#eval toString (node (leaf 10) (node (leaf 20) (leaf 30)))

-- Arrays

#eval #[1, 2, 3].map fun x => x+1
#eval #[1, 2, 3].set! 1 10
#eval #[1, 2, 3].push 4

-- Structures

structure Person :=
(name : String)
(age  : Nat := 0)

instance : ToString Person :=
⟨fun p => p.name ++ ":" ++ toString p.age⟩

#eval toString { name := "John", age := 30 : Person }

#eval toString { name := "Jack" : Person }

def incAge (p : Person) (n : Nat) : Person :=
{ p with age := p.age + n }

#eval toString $ incAge { name := "John", age := 30 } 2

-- IO

def tst (msg : String) : IO Unit := do
IO.println "hello world";
IO.println msg

#eval tst "foo"

-- Debugging helper functions

def Tree.map {α β} (f : α → β) : Tree α → Tree β
| leaf a          => leaf (f a)
| node left right => node (Tree.map left) (Tree.map right)

#print dbgTrace

#eval
  let n := node (leaf 10) (node (leaf 20) (leaf 30));
  let n := n.map fun x => x + 1;
  -- let n := n.map fun x => dbgTrace ("x: " ++ toString x) $ fun _ => x + 1;
  toString n
