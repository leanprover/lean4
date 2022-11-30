import Lean

inductive Sublist : List α → List α → Prop
  | slnil : Sublist [] []
  | cons l₁ l₂ a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
  | cons2 l₁ l₂ a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)

namespace Lean.PrefixTreeNode

namespace Ex1
inductive WellFormed (cmp : α → α → Ordering) : PrefixTreeNode α β → Prop where
  | empty_wff    : WellFormed cmp empty
  | insert_wff  {t : PrefixTreeNode α β} {k : List α} {val : β} : WellFormed cmp t → WellFormed cmp (insert t cmp k val)
end Ex1

namespace Ex2
inductive WellFormed (cmp : α → α → Ordering) : PrefixTreeNode α β → Prop where
  | empty_wff   : WellFormed cmp empty
  | insert_wff  : WellFormed cmp t → WellFormed cmp (insert t cmp k val)
end Ex2

end Lean.PrefixTreeNode
