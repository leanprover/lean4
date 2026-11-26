module

public import Lean.ConstTrie

/-!
Verification of `Lean.ImportedConsts.collectDuplicates`, the import-time sweep for names declared
by several modules. For well-formed module trees, `collectDuplicates_complete` shows that every
name occurring in two modules whose `covered` masks are disjoint is reported with both values,
and `collectDuplicates_sound` that every report lists at least two genuine declarations in
module order.
-/

open Lean ImportedConsts

namespace ConstTrieDupSpec

variable {α : Type}

/-- `c` extends `k` by exactly one component. -/
public def ExtendsOne (k c : Name) : Prop := (∃ s, c = k.str s) ∨ (∃ n, c = k.num n)

/--
A well-formed module tree: every child's key extends its parent's key by one component, and the
children of a node have pairwise distinct keys.
-/
public inductive WF : ConstTrie α → Prop
  | intro (t : ConstTrie α)
      (keys : ∀ c ∈ t.children, ExtendsOne t.key c.key)
      (distinct : t.children.toList.Pairwise (fun c₁ c₂ => c₁.key ≠ c₂.key))
      (children : ∀ c ∈ t.children, WF c) : WF t

/-- `Has t n v`: the tree `t` maps the name `n` to `v`. -/
public inductive Has : ConstTrie α → Name → α → Prop
  | here {t : ConstTrie α} {v : α} : t.val? = some v → Has t t.key v
  | child {t c : ConstTrie α} {n : Name} {v : α} : c ∈ t.children → Has c n v → Has t n v

/-- A reported duplicate is genuine: at least two entries, each a module's value for the name. -/
public def Sound (trees : Array (Nat × ConstTrie α)) (d : Duplicate α) : Prop :=
  2 ≤ d.entries.size ∧ (∀ e ∈ d.entries, ∃ t, (e.2, t) ∈ trees ∧ Has t d.name e.1) ∧
    d.entries.toList.Pairwise (fun a b => a.2 < b.2)

/--
Completeness: a name declared by two modules is reported unless a bit is set in both modules'
`covered` masks, meaning some direct import's compilation loaded both and already checked the pair.
-/
public theorem collectDuplicates_complete (trees : Array (Nat × ConstTrie α)) (covered : Array UInt64)
    (hwf : ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous)
    (hi : (i, ti) ∈ trees) (hj : (j, tj) ∈ trees) (hij : i ≠ j)
    (hvi : Has ti n vi) (hvj : Has tj n vj)
    (hcov : covered.isEmpty ∨ covered[i]! &&& covered[j]! = 0) :
    ∃ d ∈ collectDuplicates trees covered,
      d.name = n ∧ (vi, i) ∈ d.entries ∧ (vj, j) ∈ d.entries

/-- Soundness: every reported duplicate has at least two entries, all genuine, in module order. -/
public theorem collectDuplicates_sound (trees : Array (Nat × ConstTrie α)) (covered : Array UInt64)
    (hwf : ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous)
    (hord : trees.toList.Pairwise (fun a b => a.1 < b.1)) :
    ∀ d ∈ collectDuplicates trees covered, Sound trees d

end ConstTrieDupSpec
