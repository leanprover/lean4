
-- A nested inductive type
-- the `Unit → Tree α` prevents well-founded recursion

inductive Tree (α : Type u) : Type u
 | node : α → (Bool → Tree α) → List (Tree α) → Tree α


-- only recurse on the non-nested component
def Tree.simple_size : Tree α → Nat
  | .node _x t _ts => 1 + (t true).simple_size + (t false).simple_size

/--
info: theorem Tree.simple_size.eq_1.{u_1} : ∀ {α : Type u_1} (_x : α) (t : Bool → Tree α) (_ts : List (Tree α)),
  (Tree.node _x t _ts).simple_size = 1 + (t true).simple_size + (t false).simple_size :=
fun {α} _x t _ts => Eq.refl (Tree.node _x t _ts).simple_size
-/
#guard_msgs in
#print Tree.simple_size.eq_1

-- also recurse on the nested components
/--
error: fail to show termination for
  Tree.size
  Tree.aux_size
with errors
failed to infer structural recursion:
Not considering parameter α of Tree.size:
  it is unchanged in the recursive calls
Not considering parameter α of Tree.aux_size:
  it is unchanged in the recursive calls
Skipping arguments of type Tree α, as Tree.aux_size has no compatible argument.
Skipping arguments of type List (Tree α), as Tree.size has no compatible argument.


Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
Call from Tree.size to Tree.size at 25:24-37:
 #1
  ?
Call from Tree.size to Tree.size at 25:40-54:
 #1
  _
Call from Tree.size to Tree.aux_size at 25:57-68:
   #1
#2  _
Call from Tree.aux_size to Tree.size at 28:13-19:
   #2
#1  _
Call from Tree.aux_size to Tree.aux_size at 28:22-33:
 #2
  _


#1: sizeOf x1
#2: sizeOf x1

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in
mutual
def Tree.size : Tree α → Nat
  | .node _ t ts => 1 + (t true).size + (t false).size + aux_size ts
def Tree.aux_size : List (Tree α) → Nat
  | [] => 0
  | t::ts => t.size + aux_size ts
end

/--
error: fail to show termination for
  Tree.map
  Tree.map_aux
with errors
failed to infer structural recursion:
Not considering parameter α of Tree.map:
  it is unchanged in the recursive calls
Not considering parameter β of Tree.map:
  it is unchanged in the recursive calls
Not considering parameter f of Tree.map:
  it is unchanged in the recursive calls
Not considering parameter α of Tree.map_aux:
  it is unchanged in the recursive calls
Not considering parameter β of Tree.map_aux:
  it is unchanged in the recursive calls
Not considering parameter f of Tree.map_aux:
  it is unchanged in the recursive calls
Skipping arguments of type Tree α, as Tree.map_aux has no compatible argument.
Skipping arguments of type List (Tree α), as Tree.map has no compatible argument.


Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
Call from Tree.map to Tree.map at 73:42-53:
 #1
  ?
Call from Tree.map to Tree.map_aux at 73:56-68:
   #1
#2  _
Call from Tree.map_aux to Tree.map at 76:13-20:
   #2
#1  _
Call from Tree.map_aux to Tree.map_aux at 76:24-36:
 #2
  _


#1: sizeOf x1
#2: sizeOf x1

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in
mutual
def Tree.map (f : α → β) : Tree α → Tree β
  | .node x t ts => .node (f x) (fun b => (t b).map f) (map_aux f ts)
def Tree.map_aux (f : α → β) : List (Tree α) → List (Tree β)
  | [] => []
  | t::ts => t.map f :: map_aux f ts
end
