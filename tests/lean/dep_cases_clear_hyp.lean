universes u v

inductive tree (α : Type u)
| leaf {} : tree
| node (l : tree) (v : α) (r : tree) : tree

namespace tree
variables {α : Type u}

inductive is_searchable (lt : α → α → Prop) : tree α → α → α → Prop
| leaf_s  {lo hi}       : lt lo hi → is_searchable leaf lo hi
| node_s  {l r v lo hi} (hs₁ : is_searchable l lo v) (hs₂ : is_searchable r v hi) : is_searchable (node l v r) lo hi

example (l r : tree α) {lo v hi lt} (h : is_searchable lt (node l v r) lo hi) : true :=
begin
  cases h,
  trace_state, /- Should not contain h -/
  trivial
end

end tree
