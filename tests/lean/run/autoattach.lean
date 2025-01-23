prelude
import Lean.Meta.Transform
import Lean.Elab.Tactic.Simp

namespace Lean.Meta

private def getContext : MetaM Simp.Context := do
  let s : SimpTheorems := {}
  let s ← s.addConst ``dite_eq_ite (inv := true)
  Simp.mkContext
    (simpTheorems  := #[s])
    (congrTheorems := {})
    (config        := Simp.neutralConfig)

def iteToDIte2 (e : Expr) : MetaM Expr := do
  let ctx ← getContext
  let (result, _) ← Simp.main e ctx
  return result.expr

/--
info: fun n => if n > 0 then 3 else 4
fun n => if n > 0 then 3 else 4
-/
#guard_msgs in
run_elab do
  let stx ← `(fun (n : Nat) => if n > 0 then 3 else 4)
  let e ← Elab.Term.elabTerm stx .none
  let e' ← iteToDIte2 e
  logInfo m!"{e}\n{e'}"

end Lean.Meta

universe u
structure Tree (α : Type u) where
  val : α
  cs : List (Tree α)

def Tree.isLeaf (t : Tree α) := t.cs.isEmpty

/--
error: tactic 'fail' failed
α : Type u_1
t x✝ : Tree α
⊢ sizeOf x✝ < sizeOf t
-/
#guard_msgs in
def Tree.map (f : α → β) (t : Tree α) : Tree β :=
    ⟨f t.val, t.cs.map (·.map f)⟩
termination_by t
decreasing_by fail

/--
error: tactic 'fail' failed
α : Type u_1
t x✝ : Tree α
⊢ sizeOf x✝ < sizeOf t
-/
#guard_msgs in
def Tree.pruneRevAndMap (f : α → β) (t : Tree α) : Tree β :=
    ⟨f t.val, (t.cs.filter (not ·.isLeaf)).reverse.map (·.pruneRevAndMap f)⟩
termination_by t
decreasing_by fail

structure MTree (α : Type u) where
  val : α
  cs : Array (List (MTree α))

/--
error: tactic 'fail' failed
α : Type u_1
t x✝ : MTree α
⊢ sizeOf x✝ < sizeOf t
-/
#guard_msgs in
def MTree.map (f : α → β) (t : MTree α) : MTree β :=
    ⟨f t.val, t.cs.map (·.map (·.map f))⟩
termination_by t
decreasing_by fail


namespace Ex1
inductive Expression where
| var: String → Expression
| object: List (String × Expression) → Expression

/--
error: tactic 'fail' failed
L : List (String × Expression)
x : String × Expression
⊢ sizeOf x.snd < sizeOf (Expression.object L)
-/
#guard_msgs in
def t (exp: Expression): List String :=
  match exp with
  | Expression.var s => [s]
  | Expression.object L => List.foldl (fun L1 L2 => L1 ++ L2) [] (L.map (fun x => t x.2))
termination_by exp
decreasing_by fail

end Ex1
