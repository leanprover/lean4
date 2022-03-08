import Lean

inductive sublist : List α → List α → Prop
  | slnil : sublist [] []
  | cons l₁ l₂ a : sublist l₁ l₂ → sublist l₁ (a :: l₂)
  | cons2 l₁ l₂ a : sublist l₁ l₂ → sublist (a :: l₁) (a :: l₂)

namespace Lean.PrefixTreeNode

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

end Lean.PrefixTreeNode
