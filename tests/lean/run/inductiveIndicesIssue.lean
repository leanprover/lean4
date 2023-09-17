import Lean

namespace Test

open Lean

inductive sublist : List α → List α → Prop
  | slnil : sublist [] []
  | cons l₁ l₂ a : sublist l₁ l₂ → sublist l₁ (a :: l₂)
  | cons2 l₁ l₂ a : sublist l₁ l₂ → sublist (a :: l₁) (a :: l₂)

inductive PrefixTreeNode (α : Type u) (β : Type v) where
  | Node : Option β → Lean.RBNode α (fun _ => PrefixTreeNode α β) → PrefixTreeNode α β

instance : Inhabited (PrefixTreeNode α β) where
  default := PrefixTreeNode.Node none RBNode.leaf

partial def insert (t : PrefixTreeNode α β) (cmp : α → α → Ordering) (k : List α) (val : β) : PrefixTreeNode α β :=
  let rec insertEmpty (k : List α) : PrefixTreeNode α β :=
    match k with
    | [] => PrefixTreeNode.Node (some val) RBNode.leaf
    | k :: ks =>
      let t := insertEmpty ks
      PrefixTreeNode.Node none (RBNode.singleton k t)
  let rec loop
    | PrefixTreeNode.Node _ m, [] =>
      PrefixTreeNode.Node (some val) m -- overrides old value
    | PrefixTreeNode.Node v m, k :: ks =>
      let t := match RBNode.find cmp m k with
        | none   => insertEmpty ks
        | some t => loop t ks
      PrefixTreeNode.Node v (RBNode.insert cmp m k t)
  loop t k

namespace Ex1
inductive WellFormed (cmp : α → α → Ordering) : PrefixTreeNode α β → Prop where
  | emptyWff    : WellFormed cmp empty
  | insertWff  {t : PrefixTreeNode α β} {k : List α} {val : β} : WellFormed cmp t → WellFormed cmp (insert t cmp k val)
end Ex1

namespace Ex2
inductive WellFormed (cmp : α → α → Ordering) : PrefixTreeNode α β → Prop where
  | emptyWff   : WellFormed cmp empty
  | insertWff  : WellFormed cmp t → WellFormed cmp (insert t cmp k val)
end Ex2

end Test
