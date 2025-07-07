import Std

set_option warn.sorry false

open Std

/--
error: (kernel) application type mismatch
  DHashMap.Raw.WF inner
argument has type
  _nested.Std.DHashMap.Raw_3
but function has type
  (DHashMap.Raw String fun x => HashMapTree') → Prop
-/
#guard_msgs in
structure HashMapTree' where
  node : HashMap String HashMapTree'

/--
error: (kernel) application type mismatch
  DHashMap.Raw.WF inner
argument has type
  _nested.Std.DHashMap.Raw_2
but function has type
  (DHashMap.Raw String fun x => DHashMapTree') → Prop
-/
#guard_msgs in
structure DHashMapTree' where
  node : DHashMap String (fun _ => DHashMapTree')

structure DHashMapRawTree where
  node : DHashMap.Raw String (fun _ => DHashMapRawTree)

inductive List.Forall {α : Type u} (p : α → Prop) : List α → Prop
  | nil : List.Forall p []
  | cons {x xs} : p x → xs.Forall p → List.Forall p (x :: xs)

inductive Array.Forall {α : Type u} (p : α → Prop) : Array α → Prop
  | mk xs : xs.Forall p → Array.Forall p (.mk xs)

inductive Std.DHashMap.Internal.AssocList.Forall {α : Type u} {β : α → Type v} (p : ∀ s, β s → Prop) :
  Std.DHashMap.Internal.AssocList α β → Prop
  | nil : DHashMap.Internal.AssocList.nil.Forall p
  | cons key value tail :
    p key value →
    tail.Forall p →
    (DHashMap.Internal.AssocList.cons key value tail).Forall p

inductive Std.DHashMap.Raw.Forall {α : Type u} {β : α → Type v} (p : ∀ s, β s → Prop) : DHashMap.Raw α β → Prop
  | mk size buckets : buckets.Forall (·.Forall p) → (Std.DHashMap.Raw.mk size buckets).Forall p

theorem Std.DHashMap.Raw.Forall_of_forall {α : Type u} {β : α → Type v}  (p : ∀ a, β a → Prop)
    (h : ∀ a x, p a x) (m : DHashMap.Raw α β) : m.Forall p :=
  sorry

theorem Std.DHashMap.Raw.Forall_map {α : Type u} {β : α → Type v} {γ : α → Type w}
  (f : ∀ a, β a → γ a) (p : ∀ a, γ a → Prop)
  (m : DHashMap.Raw α β)
  (h : m.Forall (fun a x => p a (f a x))) :
  (DHashMap.Raw.Forall p (m.map f)) :=
  sorry

-- Std only has `map_map_equiv`. Can we have equality here?
theorem Std.DHashMap.Raw.map_map {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : α → Type uu} {f : (a : α) → β a → γ a} {g : (a : α) → γ a → δ a}
  (m : DHashMap.Raw α β) : (m.map f).map g = m.map fun k v => g k (f k v) := by
  sorry

theorem Std.DHashMap.Raw.map_id {α : Type u} {β : α → Type v} (m : DHashMap.Raw α β) :
  m.map (fun _ x => x) = m := by
  sorry

inductive DHashMapRawTree.WF : DHashMapRawTree → Prop
  | mk node :
    (wf : node.WF) →
    (h : node.Forall (fun _ v => DHashMapRawTree.WF v)) →
    (DHashMapRawTree.mk node).WF

theorem DHashMapRawTree.WF.wf (node : DHashMap.Raw String fun _ => DHashMapRawTree)
  (h : DHashMapRawTree.WF (.mk node)) : node.WF := by cases h ; assumption

theorem DHashMapRawTree.WF.h (node : DHashMap.Raw String fun _ => DHashMapRawTree)
  (h : DHashMapRawTree.WF (.mk node)) : node.Forall (fun _ v => DHashMapRawTree.WF v) := by cases h ; assumption

structure DHashMapTree where mk' ::
  inner : DHashMapRawTree
  wf : inner.WF

def DHashMapTree.rep : DHashMapTree → DHashMapRawTree :=
  fun t => t.inner

/-- Fake constructor -/
def DHashMapTree.mk (node : DHashMap String (fun _ => DHashMapTree)) : DHashMapTree where
  inner := .mk (node.inner.map (fun _ t => t.inner))
  wf := by
    apply DHashMapRawTree.WF.mk
    case wf =>
      apply DHashMap.Raw.WF.map
      apply node.wf
    case h =>
      apply Std.DHashMap.Raw.Forall_map
      apply Std.DHashMap.Raw.Forall_of_forall
      intro key node
      apply node.wf

/-- Fake casesOn -/
def DHashMapTree.casesOn'
  (motive : DHashMapTree → Sort u)
  (mk : (node : DHashMap String (fun _ => DHashMapTree)) → motive (.mk node))
  (t : DHashMapTree) : motive t :=
  t.casesOn fun inner wf =>
    inner.casesOn (motive_1 := fun inner => (wf : inner.WF) → motive ⟨inner, wf⟩) (wf := wf)
      fun node wf => by
      specialize mk ⟨?foo, ?wf⟩
      case foo =>
        exact node.map fun _ t => by
          apply DHashMapTree.mk' t
          sorry -- needs a variant of attach or pmap?
      case wf =>
        apply DHashMap.Raw.WF.map
        exact wf.wf
      unfold DHashMapTree.mk at mk
      dsimp only at mk
      -- Not an equality, just an equiv!
      -- rw [DHashMap.Raw.map_map] at mk
      -- But still rewriting, causing DTT below
      simp only [DHashMap.Raw.map_map, DHashMap.Raw.map_id] at mk
      cases inner <;> exact mk -- why no structure eta here?

-- For non-dependent motives we can prove the equality
theorem DHashMapTree.casesOn'_eq1_nondep
  (motive : Sort u) mk (node : DHashMap String (fun _ => DHashMapTree)) :
  DHashMapTree.casesOn' (fun _ => motive) mk (.mk node) = mk node := by
  cases node
  unfold DHashMapTree.casesOn' DHashMapTree.mk
  simp
  congr
  simp [DHashMap.Raw.map_map, DHashMap.Raw.map_id]

theorem cast_congrArg_mk
  {T : Type w}
  {S : Type v}
  (f : T → S)
  (motive : S → Sort u)
  (g : (node : T) → motive (f node))
  (m n : T) (h : m = n) : cast (congrArg (fun x => motive (f x)) h) (g m) = g n := by
  cases h
  rfl


-- For dependent motives we need the tricky cast_congr_thing above
theorem DHashMapTree.casesOn'_eq1
  (motive : DHashMapTree → Sort u) mk (node : DHashMap String (fun _ => DHashMapTree)) :
  DHashMapTree.casesOn' motive mk (.mk node) = mk node := by
  unfold DHashMapTree.casesOn' DHashMapTree.mk
  simp
  apply cast_congrArg_mk
  simp [DHashMap.Raw.map_map, DHashMap.Raw.map_id]

-- What should the recursor be? Something like this?
-- Or some Type-valued `node.Forall motive`?
def DHashMapTree.rec'
    (motive : DHashMapTree → Type u)
    (mk :
      (node : DHashMap String (fun _ => (t : DHashMapTree) ×' motive t)) →
       motive (.mk (node.map (fun _ t => t.1))))
    (t : DHashMapTree) : motive t :=
  sorry
