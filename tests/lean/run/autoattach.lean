universe u
structure Tree (α : Type u) where
  val : α
  cs : List (Tree α)

def Tree.isLeaf (t : Tree α) := t.cs.isEmpty

/--
info: α : Type u_1
t x : Tree α
h : x ∈ t.cs
⊢ sizeOf x < sizeOf t
-/
#guard_msgs in
def Tree.map (f : α → β) (t : Tree α) : Tree β :=
    ⟨f t.val, t.cs.map (·.map f)⟩
termination_by t
decreasing_by trace_state; cases t; decreasing_tactic


/--
info: α : Type u_1
t x : Tree α
h : x ∈ t.cs
⊢ sizeOf x < sizeOf t
-/
#guard_msgs in
def Tree.pruneRevAndMap (f : α → β) (t : Tree α) : Tree β :=
    ⟨f t.val, (t.cs.filter (not ·.isLeaf)).reverse.map (·.pruneRevAndMap f)⟩
termination_by t
decreasing_by trace_state; cases t; decreasing_tactic

structure MTree (α : Type u) where
  val : α
  cs : Array (List (MTree α))

-- set_option trace.Elab.definition.wf true in
/--
error: tactic 'fail' failed
case mk
α : Type u_1
x✝ : List (MTree α)
x : MTree α
h✝ : x ∈ x✝
val✝ : α
cs✝ : Array (List (MTree α))
h : x✝ ∈ cs✝
⊢ sizeOf x✝ ≤ sizeOf cs✝ + 1
---
info: α : Type u_1
t : MTree α
x✝ : List (MTree α)
h✝ : x✝ ∈ t.cs
x : MTree α
h : x ∈ x✝
⊢ sizeOf x < sizeOf t
-/
#guard_msgs in
def MTree.map (f : α → β) (t : MTree α) : MTree β :=
    ⟨f t.val, t.cs.map (·.map (·.map f))⟩
termination_by t
decreasing_by trace_state; cases t; simp at *; decreasing_tactic; fail

namespace Ex1
inductive Expression where
| var: String → Expression
| object: List (String × Expression) → Expression

/--
error: unsolved goals
L : List (String × Expression)
x : String × Expression
⊢ sizeOf x.snd < sizeOf (Expression.object L)
-/
#guard_msgs in
def t (exp: Expression) : List String :=
  match exp with
  | Expression.var s => [s]
  | Expression.object L => List.foldl (fun L1 L2 => L1 ++ L2) [] (L.map (fun x => t x.2))
termination_by exp
decreasing_by skip

end Ex1
