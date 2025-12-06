/--
Colors of red black tree nodes.
-/
inductive Color where
  | black
  | red

/--
The basic red black tree data structure without any invariant etc. attached.
-/
inductive Raw (α : Type u) where
  /--
  The empty tree.
  -/
  | nil : Raw α
  /--
  A node with left and right successor, its color and a piece of data
  -/
  | node (left : Raw α) (data : α) (color : Color) (right : Raw α) : Raw α

namespace Raw

/--
Paint the color of the root of `t` to given color `c`.
-/
@[inline]
def paintColor (c : Color) (t : Raw α) : Raw α :=
  match t with
  | .nil => .nil
  | .node l d _ r => .node l d c r

-- Balanced insert into the left child, fixing red on red sequences on the way.
@[inline]
def baliL (d : α) : Raw α → Raw α → Raw α
  | .node (.node t₁ data₁ .red t₂) data₂ .red t₃, right
  | .node t₁ data₁ .red (.node t₂ data₂ .red t₃), right =>
      .node (.node t₁ data₁ .black t₂) data₂ .red (.node t₃ d .black right)
  | left, right => .node left d .black right

-- Balanced insert into the right child, fixing red on red sequences on the way.
@[inline]
def baliR (d : α) : Raw α → Raw α → Raw α
  | left, .node t₁ data₁ .red (.node t₂ data₂ .red t₃)
  | left, .node (.node t₁ data₁ .red t₂) data₂ .red t₃ =>
      .node (.node left d .black t₁) data₁ .red (.node t₂ data₂ .black t₃)
  | left, right => .node left d .black right

-- Balance a tree on the way up from deletion, prioritizing the left side.
def baldL (d : α) : Raw α → Raw α → Raw α
  | .node t₁ data .red t₂, right =>
      .node (.node t₁ data .black t₂) d .red right
  | left, .node t₁ data .black t₂ =>
      baliR d left (.node t₁ data .red t₂)
  | left, .node (.node t₁ data₁ .black t₂) data₂ .red t₃ =>
      .node (.node left d .black t₁) data₁ .red (baliR data₂ t₂ (paintColor .red t₃))
  | left, right => .node left d .red right

-- Balance a tree on the way up from deletion, prioritizing the right side.
def baldR (d : α) : Raw α → Raw α → Raw α
  | left, .node t₁ data .red t₂ =>
      .node left d .red (.node t₁ data .black t₂)
  | .node t₁ data .black t₂, right =>
      baliL d (.node t₁ data .red t₂) right
  | .node  t₁ data₁ .red (.node t₂ data₂ .black t₃), right =>
      .node (baliL data₁ (paintColor .red t₁) t₂) data₁ .red (.node t₃ data₂ .black right)
  | left, right => .node left d .red right

-- Appends one tree to another while painting the correct color
def appendTrees : Raw α → Raw α → Raw α
  | .nil, t => t
  | t, .nil => t
  | .node left₁ data₁ .red right₁, .node left₂ data₂ .red right₂ =>
    match appendTrees right₁ left₂ with
    | .node left₃ data₃ .red right₃ =>
        .node (.node left₁ data₁ .red left₃) data₃ .red (.node right₃ data₂ .red right₂)
    | t                   => .node left₁ data₁ .red (.node t data₂ .red right₂)
  | .node left₁ data₁ .black right₁, .node left₂ data₂ .black right₂ =>
    match appendTrees right₁ left₂ with
    | .node left₃ data₃ .red right₃ =>
        .node (node left₁ data₁ .black left₃) data₃ .red (node right₃ data₂ .black right₂)
    | t                   => baldL data₁ left₁ (node t data₂ .black right₂)
  | t, .node left data .red right => node (appendTrees t left) data .red right
  | .node left data .red right, t => .node left data .red (appendTrees right t)

def del [Ord α] (d : α) : Raw α → Raw α
  | .nil => .nil
  | .node left data _ right =>
    match compare d data with
    | .lt =>
      match left with
      | .node _ _ .black _ => baldL data (del d left) right
      | _ => .node (del d left) data .red right
    | .eq => appendTrees left right
    | .gt =>
      match right with
      | .node _ _ .black _ => baldR data left (del d right)
      | _ => .node left data .red (del d right)


/--
info: equations:
@[defeq] theorem Raw.del.eq_1.{u_1} : ∀ {α : Type u_1} [inst : Ord α] (d : α), del d nil = nil
@[defeq] theorem Raw.del.eq_2.{u_1} : ∀ {α : Type u_1} [inst : Ord α] (d d_1 : α) (color : Color) (left_1 : Raw α)
  (data : α) (right left_3 : Raw α) (data_1 : α) (right_1 : Raw α),
  del d ((left_1.node data Color.black right).node d_1 color (left_3.node data_1 Color.black right_1)) =
    match compare d d_1 with
    | Ordering.lt => baldL d_1 (del d (left_1.node data Color.black right)) (left_3.node data_1 Color.black right_1)
    | Ordering.eq => (left_1.node data Color.black right).appendTrees (left_3.node data_1 Color.black right_1)
    | Ordering.gt => baldR d_1 (left_1.node data Color.black right) (del d (left_3.node data_1 Color.black right_1))
theorem Raw.del.eq_3.{u_1} : ∀ {α : Type u_1} [inst : Ord α] (d d_1 : α) (color : Color) (r left_1 : Raw α) (data : α)
  (right : Raw α),
  (∀ (left : Raw α) (data : α) (right : Raw α), r = left.node data Color.black right → False) →
    del d ((left_1.node data Color.black right).node d_1 color r) =
      match compare d d_1 with
      | Ordering.lt => baldL d_1 (del d (left_1.node data Color.black right)) r
      | Ordering.eq => (left_1.node data Color.black right).appendTrees r
      | Ordering.gt => (left_1.node data Color.black right).node d_1 Color.red (del d r)
theorem Raw.del.eq_4.{u_1} : ∀ {α : Type u_1} [inst : Ord α] (d : α) (l : Raw α) (d_1 : α) (color : Color)
  (left_2 : Raw α) (data : α) (right : Raw α),
  (∀ (left : Raw α) (data : α) (right : Raw α), l = left.node data Color.black right → False) →
    del d (l.node d_1 color (left_2.node data Color.black right)) =
      match compare d d_1 with
      | Ordering.lt => (del d l).node d_1 Color.red (left_2.node data Color.black right)
      | Ordering.eq => l.appendTrees (left_2.node data Color.black right)
      | Ordering.gt => baldR d_1 l (del d (left_2.node data Color.black right))
theorem Raw.del.eq_5.{u_1} : ∀ {α : Type u_1} [inst : Ord α] (d : α) (l : Raw α) (d_1 : α) (color : Color) (r : Raw α),
  (∀ (left : Raw α) (data : α) (right : Raw α), l = left.node data Color.black right → False) →
    (∀ (left : Raw α) (data : α) (right : Raw α), r = left.node data Color.black right → False) →
      del d (l.node d_1 color r) =
        match compare d d_1 with
        | Ordering.lt => (del d l).node d_1 Color.red r
        | Ordering.eq => l.appendTrees r
        | Ordering.gt => l.node d_1 Color.red (del d r)
-/
#guard_msgs in
#print equations del
