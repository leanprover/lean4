set_option Elab.async false -- for stable output order in #guard_msgs

universe u
structure Tree (α : Type u) where
  val : α
  cs : List (Tree α)

def Tree.isLeaf (t : Tree α) := t.cs.isEmpty

/--
info: α : Type u_1
t t' : Tree α
h✝ : t' ∈ t.cs
⊢ sizeOf t' < sizeOf t
-/
#guard_msgs in
def Tree.map (f : α → β) (t : Tree α) : Tree β :=
    ⟨f t.val, t.cs.map (fun t' => t'.map f)⟩
termination_by t
decreasing_by trace_state; cases t; decreasing_tactic

/--
info: equations:
theorem Tree.map.eq_1.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (t : Tree α),
  Tree.map f t = { val := f t.val, cs := List.map (fun t' => Tree.map f t') t.cs }
-/
#guard_msgs in
#print equations Tree.map

/--
info: Tree.map.induct.{u_1} {α : Type u_1} (motive : Tree α → Prop)
  (case1 : ∀ (x : Tree α), (∀ (t' : Tree α), t' ∈ x.cs → motive t') → motive x) (t : Tree α) : motive t
-/
#guard_msgs in
#check Tree.map.induct

/--
info: α : Type u_1
t x✝ : Tree α
h✝ : x✝ ∈ t.cs
⊢ sizeOf x✝ < sizeOf t
-/
#guard_msgs in
def Tree.pruneRevAndMap (f : α → β) (t : Tree α) : Tree β :=
    ⟨f t.val, (t.cs.filter (fun t' => not t'.isLeaf)).reverse.map (·.pruneRevAndMap f)⟩
termination_by t
decreasing_by trace_state; cases t; decreasing_tactic

/--
info: equations:
theorem Tree.pruneRevAndMap.eq_1.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (t : Tree α),
  Tree.pruneRevAndMap f t =
    { val := f t.val,
      cs := List.map (fun x => Tree.pruneRevAndMap f x) (List.filter (fun t' => !t'.isLeaf) t.cs).reverse }
-/
#guard_msgs in
#print equations Tree.pruneRevAndMap

/--
info: Tree.pruneRevAndMap.induct.{u_1} {α : Type u_1} (motive : Tree α → Prop)
  (case1 : ∀ (x : Tree α), (∀ (x_1 : Tree α), x_1 ∈ x.cs → motive x_1) → motive x) (t : Tree α) : motive t
-/
#guard_msgs in
#check Tree.pruneRevAndMap.induct

/--
info: α : Type u_1
v : α
cs : List (Tree α)
x✝ : Tree α
h✝ : x✝ ∈ cs
⊢ sizeOf x✝ < sizeOf { val := v, cs := cs }
-/
#guard_msgs in
def Tree.pruneRevAndMap' (f : α → β) : Tree α → Tree β
  | ⟨v,cs⟩ => ⟨f v, (cs.filter (fun t' => not t'.isLeaf)).reverse.map (·.pruneRevAndMap' f)⟩
termination_by t => t
decreasing_by trace_state; decreasing_tactic

/--
info: equations:
theorem Tree.pruneRevAndMap'.eq_1.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (v : α) (cs : List (Tree α)),
  Tree.pruneRevAndMap' f { val := v, cs := cs } =
    { val := f v, cs := List.map (fun x => Tree.pruneRevAndMap' f x) (List.filter (fun t' => !t'.isLeaf) cs).reverse }
-/
#guard_msgs in
#print equations Tree.pruneRevAndMap'

/--
info: Tree.pruneRevAndMap'.induct.{u_1} {α : Type u_1} (motive : Tree α → Prop)
  (case1 : ∀ (v : α) (cs : List (Tree α)), (∀ (x : Tree α), x ∈ cs → motive x) → motive { val := v, cs := cs })
  (a✝ : Tree α) : motive a✝
-/
#guard_msgs in
#check Tree.pruneRevAndMap'.induct

-- Check that wfParam propagates through let-expressions

/--
error: failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
t : Tree α
children : List (Tree α) := t.cs
c : Tree α
h✝ : c ∈ children
⊢ sizeOf c < sizeOf t
-/
#guard_msgs in
def Tree.depth (t : Tree α) : Nat :=
  let children := t.cs
  let depths := children.map fun c => Tree.depth c
  match depths.max? with
  | some d => d+1
  | none => 0
termination_by t

structure MTree (α : Type u) where
  val : α
  cs : Array (List (MTree α))

-- set_option trace.Elab.definition.wf true in
/--
warning: declaration uses 'sorry'
---
info: α : Type u_1
t : MTree α
x✝¹ : List (MTree α)
h✝¹ : x✝¹ ∈ t.cs
x✝ : MTree α
h✝ : x✝ ∈ x✝¹
⊢ sizeOf x✝ < sizeOf t
-/
#guard_msgs in
def MTree.map (f : α → β) (t : MTree α) : MTree β :=
    ⟨f t.val, t.cs.map (·.map (·.map f))⟩
termination_by t
decreasing_by trace_state; cases t; simp at *; decreasing_tactic; sorry

/--
info: equations:
theorem MTree.map.eq_1.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (t : MTree α),
  MTree.map f t = { val := f t.val, cs := Array.map (fun x => List.map (fun x => MTree.map f x) x) t.cs }
-/
#guard_msgs in
#print equations MTree.map

/--
info: MTree.map.induct.{u_1} {α : Type u_1} (motive : MTree α → Prop)
  (case1 : ∀ (x : MTree α), (∀ (x_1 : List (MTree α)), x_1 ∈ x.cs → ∀ (x : MTree α), x ∈ x_1 → motive x) → motive x)
  (t : MTree α) : motive t
-/
#guard_msgs in
#check MTree.map.induct

/--
info: α : Type u_1
t : MTree α
css : List (MTree α)
h✝¹ : css ∈ t.cs
c : MTree α
h✝ : c ∈ css
⊢ sizeOf c < sizeOf t
-/
#guard_msgs in
def MTree.size (t : MTree α) : Nat := Id.run do
  let mut s := 1
  for css in t.cs do
    for c in css do
      s := s + c.size
  pure s
termination_by t
decreasing_by
  trace_state
  fail_if_success grind -- eventually, grind should be able to handle this
  cases t
  have := Array.sizeOf_lt_of_mem ‹_ ∈ _›
  have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  simp only [mk.sizeOf_spec, sizeOf_default, Nat.add_zero, gt_iff_lt] at *
  omega

/--
info: equations:
theorem MTree.size.eq_1.{u_1} : ∀ {α : Type u_1} (t : MTree α),
  t.size =
    (let s := 1;
      do
      let r ←
        forIn t.cs s fun css r =>
            let s := r;
            do
            let r ←
              forIn css s fun c r =>
                  let s := r;
                  let s := s + c.size;
                  do
                  pure PUnit.unit
                  pure (ForInStep.yield s)
            let s : Nat := r
            pure PUnit.unit
            pure (ForInStep.yield s)
      let s : Nat := r
      pure s).run
-/
#guard_msgs in
#print equations MTree.size

/--
info: MTree.size.induct.{u_1} {α : Type u_1} (motive : MTree α → Prop)
  (case1 : ∀ (x : MTree α), (∀ (css : List (MTree α)), css ∈ x.cs → ∀ (c : MTree α), c ∈ css → motive c) → motive x)
  (t : MTree α) : motive t
-/
#guard_msgs in
#check MTree.size.induct

namespace Ex1
inductive Expression where
| var: String → Expression
| object: List (String × Expression) → Expression

/--
warning: declaration uses 'sorry'
---
info: L : List (String × Expression)
x : String × Expression
h✝ : x ∈ L
⊢ sizeOf x.snd < sizeOf (Expression.object L)
-/
#guard_msgs in
def t (exp: Expression) : List String :=
  match exp with
  | Expression.var s => [s]
  | Expression.object L => List.foldl (fun L1 L2 => L1 ++ L2) [] (L.map (fun x => t x.2))
termination_by exp
decreasing_by trace_state; sorry

/--
info: equations:
theorem Ex1.t.eq_1 : ∀ (s : String), t (Expression.var s) = [s]
theorem Ex1.t.eq_2 : ∀ (L : List (String × Expression)),
  t (Expression.object L) = List.foldl (fun L1 L2 => L1 ++ L2) [] (List.map (fun x => t x.snd) L)
-/
#guard_msgs in
#print equations t

/--
info: Ex1.t.induct (motive : Expression → Prop) (case1 : ∀ (s : String), motive (Expression.var s))
  (case2 :
    ∀ (L : List (String × Expression)), (∀ (x : String × Expression), motive x.snd) → motive (Expression.object L))
  (exp : Expression) : motive exp
-/
#guard_msgs in
#check t.induct

end Ex1

namespace Ex2
inductive Expression where
| var: String → Expression
| object: List (String × Expression) → Expression

/--
warning: declaration uses 'sorry'
---
info: L : List (String × Expression)
x : String × Expression
h✝ : x ∈ L
⊢ sizeOf x.snd < sizeOf (Expression.object L)
-/
#guard_msgs in
def t (exp: Expression) : List String :=
  match exp with
  | Expression.var s => [s]
  | Expression.object L => L.foldl (fun L1 x => L1 ++ t x.2) []
termination_by exp
decreasing_by trace_state; sorry

end Ex2


namespace WithOptionOff

set_option wf.preprocess false

/--
error: tactic 'fail' failed
α : Type u_1
t t' : Tree α
⊢ sizeOf t' < sizeOf t
-/
#guard_msgs in
def map (f : α → β) (t : Tree α) : Tree β :=
    ⟨f t.val, t.cs.map (fun t' => map f t')⟩
termination_by t
decreasing_by fail

end WithOptionOff
