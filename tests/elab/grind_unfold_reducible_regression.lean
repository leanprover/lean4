module
public import Std.Data.ExtTreeMap
public section
open Std

/--
An extensional tree map with a default value.

To preserve extensionality, we require that the default value is not present in the tree.

**Implementation note**: we use `Ord α` rather than a `cmp : α → α → Ordering` argument,
because `grind` can not instantiate `ReflCmp` and `TransCmp` theorems because there is no constant to key on.
-/
structure TreeMapD (α : Type u) [Ord α] [TransOrd α] (β : Type v) (d : β) where
  tree : ExtTreeMap α β compare
  no_default : ∀ a : α, tree[a]? ≠ some d := by grind

namespace TreeMapD

variable {α : Type u} [Ord α] [TransOrd α] {β : Type v} {d : β}

instance : GetElem (TreeMapD α β d) α β (fun _ _ => True) where
  getElem := fun m a _ => m.tree[a]?.getD d

@[local grind] private theorem getElem_mk
    (tree : ExtTreeMap α β compare) (no_default : ∀ a : α, tree[a]? ≠ some d) (a : α) :
    (TreeMapD.mk tree no_default)[a] = tree[a]?.getD d := rfl

@[local grind] private theorem getElem?_tree [DecidableEq β] (m : TreeMapD α β d) (a : α) :
    m.tree[a]? = if m[a] = d then none else some m[a] := by
  grind [cases TreeMapD]

@[local grind] private theorem mem_tree (m : TreeMapD α β d) (a : α) :
    a ∈ m.tree ↔ m[a] ≠ d := by
  grind [cases TreeMapD]

@[ext, grind ext]
theorem ext [LawfulEqOrd α] {m₁ m₂ : TreeMapD α β d} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rcases m₁ with ⟨tree₁, no_default₁⟩
  rcases m₂ with ⟨tree₂, no_default₂⟩
  congr
  ext a b
  specialize h a
  grind

def empty : TreeMapD α β d where
  tree := ∅

instance : EmptyCollection (TreeMapD α β d) :=
  ⟨empty⟩

@[grind =] theorem empty_eq_emptyc : (empty : TreeMapD α β d) = ∅ := rfl

instance : Inhabited (TreeMapD α β d) :=
  ⟨empty⟩

@[grind =] theorem getElem_empty (a : α) : (∅ : TreeMapD α β d)[a] = d := (rfl)

variable [DecidableEq β]

def insert (m : TreeMapD α β d) (a : α) (b : β) : TreeMapD α β d where
  tree := if b = d then m.tree.erase a else m.tree.insert a b
  no_default := by
    -- `grind` can't do this split because of the dependent typing in the `xs[i]?` notation.
    split <;> grind

@[grind =] theorem getElem_insert [DecidableEq α] [LawfulEqOrd α] (m : TreeMapD α β d) (a : α) (b : β) :
    (m.insert a b)[k] = if k = a then b else m[k] := by
  grind [insert]
