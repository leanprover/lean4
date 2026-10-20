import rc_model
import Init.Data.List.Erase
import Init.Data.List.FinRange

/-!
An executable model of the reference-counting deletion worklist in `runtime/object.cpp`.

Each root and each field occurrence has a distinct ownership token. Counts are derived from these
tokens, including fields of objects awaiting deletion. `none` in `rc` means that an object has lost
its last reference; its storage is reclaimed only after its fields have been scanned.

The graph is immutable during a cascade. Atomics are modeled at their linearization points using
`rc_model`; task scheduling and arbitrary external finalizer effects are outside this model.
-/

namespace RcGraph

inductive Token (roots fields : Nat) where
  | root : Fin roots → Token roots fields
  | field : Fin fields → Token roots fields
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

structure Graph (α : Type) (objects roots fields : Nat) where
  payload : Fin objects → α
  root : Fin roots → Fin objects
  source : Fin fields → Fin objects
  target : Fin fields → Fin objects

abbrev Ownership roots fields := List (Token roots fields)

def Graph.dst (g : Graph α objects roots fields) : Token roots fields → Fin objects
  | .root r => g.root r
  | .field f => g.target f

def Graph.children (g : Graph α objects roots fields) (o : Fin objects) :
    List (Fin fields) :=
  (List.finRange fields).filter fun f => g.source f == o

def count (g : Graph α objects roots fields) (own : Ownership roots fields)
    (o : Fin objects) : Nat :=
  own.countP fun t => g.dst t == o

def idealCell (g : Graph α objects roots fields) (own : Ownership roots fields)
    (o : Fin objects) : Option Nat :=
  let n := count g own o
  if n = 0 then none else some n

structure State (objects roots fields : Nat) where
  own : Ownership roots fields
  rc : Fin objects → Option Int32
  todo : List (Fin objects) := []
  freed : List (Fin objects) := []

def weight (s : State objects roots fields) : Nat := s.own.length + s.todo.length

/-- Every counted reference has an owner; live objects retain all their fields. -/
def Valid (g : Graph α objects roots fields) (s : State objects roots fields) : Prop :=
  s.own.Nodup ∧
  (∀ f, (s.rc (g.source f)).isSome → .field f ∈ s.own) ∧
  ∀ o, tracks (s.rc o) (idealCell g s.own o)

/-- A field may be dropped only after its source loses its last reference. -/
def Droppable (g : Graph α objects roots fields) (s : State objects roots fields) :
    Token roots fields → Prop
  | .root _ => True
  | .field f => s.rc (g.source f) = none

def set (rc : Fin objects → Option Int32) (o : Fin objects) (v : Option Int32) :=
  fun p => if p = o then v else rc p

/--
Consume one owned reference. A last-reference transition pushes the target onto the LIFO worklist.
The guards make the function total on malformed inputs; validity proves they do not discard work.
-/
def drop (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : State objects roots fields :=
  if t ∈ s.own then
    let s := { s with own := s.own.erase t }
    match s.rc (g.dst t) with
    | none => s
    | some rc =>
      match decRef rc with
      | none => { s with rc := set s.rc (g.dst t) none, todo := g.dst t :: s.todo }
      | some rc' => { s with rc := set s.rc (g.dst t) (some rc') }
  else s

private theorem count_erase (g : Graph α objects roots fields)
    {own : Ownership roots fields} {t : Token roots fields} (ht : t ∈ own) (o : Fin objects) :
    count g own o = count g (own.erase t) o + if g.dst t == o then 1 else 0 := by
  simpa only [count, List.countP_cons] using
    (List.perm_cons_erase ht).countP_eq (fun t => g.dst t == o)

private theorem count_pos {g : Graph α objects roots fields}
    {own : Ownership roots fields} {t : Token roots fields} (ht : t ∈ own) :
    0 < count g own (g.dst t) := by
  simp only [count, List.countP_pos_iff]
  exact ⟨t, ht, by simp⟩

theorem token_live {g : Graph α objects roots fields} {s : State objects roots fields}
    (hv : Valid g s) {t : Token roots fields} (ht : t ∈ s.own) :
    (s.rc (g.dst t)).isSome := by
  have hpos := count_pos (g := g) ht
  have htrack := hv.2.2 (g.dst t)
  cases hc : s.rc (g.dst t) <;> simp_all [idealCell, tracks]

@[simp] theorem drop_own (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : (drop g s t).own = s.own.erase t := by
  unfold drop
  split
  · dsimp only
    split <;> (try split) <;> rfl
  · simp_all [List.erase_of_not_mem]

@[simp] theorem drop_freed (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : (drop g s t).freed = s.freed := by
  unfold drop
  split <;> dsimp only <;> (try split) <;> (try split) <;> rfl

theorem drop_rc_other (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) {o : Fin objects} (hne : o ≠ g.dst t) :
    (drop g s t).rc o = s.rc o := by
  unfold drop
  split <;> dsimp only <;> (try split) <;> (try split) <;> simp_all [set]

theorem drop_rc_none (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) {o : Fin objects} (h : s.rc o = none) :
    (drop g s t).rc o = none := by
  by_cases heq : o = g.dst t
  · subst o
    unfold drop
    split <;> simp [h]
  · rw [drop_rc_other _ _ _ heq, h]

theorem drop_live_before {g : Graph α objects roots fields} {s : State objects roots fields}
    {t : Token roots fields} {o : Fin objects} (h : ((drop g s t).rc o).isSome) :
    (s.rc o).isSome := by
  cases hs : s.rc o with
  | none => simp [drop_rc_none _ _ _ hs] at h
  | some rc => rfl

theorem drop_rc_target {g : Graph α objects roots fields} {s : State objects roots fields}
    {t : Token roots fields} (ht : t ∈ s.own) :
    (drop g s t).rc (g.dst t) = (s.rc (g.dst t)).bind decRef := by
  unfold drop
  simp only [ht, ↓reduceIte]
  split <;> (try split) <;> simp_all [set]

private theorem idealCell_erase_target {g : Graph α objects roots fields}
    {own : Ownership roots fields} {t : Token roots fields} (ht : t ∈ own) :
    idealCell g (own.erase t) (g.dst t) = (idealCell g own (g.dst t)).bind Op.dec.applyIdeal := by
  have hp := count_pos (g := g) ht
  have hc := count_erase g ht (g.dst t)
  simp only [beq_self_eq_true, ↓reduceIte] at hc
  simp only [idealCell]
  split <;> split <;> simp_all <;> omega

theorem drop_valid {g : Graph α objects roots fields} {s : State objects roots fields}
    {t : Token roots fields} (hv : Valid g s) (hd : Droppable g s t) :
    Valid g (drop g s t) := by
  by_cases ht : t ∈ s.own
  · refine ⟨by simpa using hv.1.erase t, ?_, ?_⟩
    · intro f hf
      have hf' := drop_live_before hf
      rw [drop_own]
      apply List.mem_erase_of_ne _ |>.2 (hv.2.1 f hf')
      intro heq
      subst t
      simp [Droppable] at hd
      simp [hd] at hf'
    · intro o
      rw [drop_own]
      by_cases heq : o = g.dst t
      · subst o
        rw [drop_rc_target ht, idealCell_erase_target ht]
        exact tracks_step .dec _ _ (hv.2.2 _)
      · rw [drop_rc_other _ _ _ heq]
        have hc := count_erase g ht o
        simp only [show (g.dst t == o) = false by simp [Ne.symm heq],
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc
        simpa only [idealCell, ← hc] using hv.2.2 o
  · simpa [drop, ht] using hv

/-- Each consumed token pays for at most one newly queued object. -/
theorem drop_weight (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : weight (drop g s t) ≤ weight s := by
  by_cases ht : t ∈ s.own
  · have hlen := List.length_erase_of_mem ht
    have hpos := List.length_pos_of_mem ht
    unfold drop weight
    simp only [ht, ↓reduceIte]
    split <;> (try split) <;> simp_all <;> omega
  · simp [drop, ht]

/-- Scan fields from left to right, pushing newly dead targets at the head of the worklist. -/
def scan (g : Graph α objects roots fields) (s : State objects roots fields)
    (fs : List (Fin fields)) : State objects roots fields :=
  fs.foldl (fun s f => drop g s (.field f)) s

theorem scan_none {g : Graph α objects roots fields} {s : State objects roots fields}
    {o : Fin objects} (h : s.rc o = none) (fs : List (Fin fields)) :
    (scan g s fs).rc o = none := by
  induction fs generalizing s with
  | nil => exact h
  | cons f fs ih => exact ih (drop_rc_none _ _ _ h)

theorem scan_valid {g : Graph α objects roots fields} {s : State objects roots fields}
    (hv : Valid g s) (fs : List (Fin fields))
    (hd : ∀ f ∈ fs, s.rc (g.source f) = none) : Valid g (scan g s fs) := by
  induction fs generalizing s with
  | nil => exact hv
  | cons f fs ih =>
    apply ih (drop_valid (t := .field f) hv (hd f (by simp)))
    intro f' hf'
    exact drop_rc_none _ _ _ (hd f' (by simp [hf']))

@[simp] theorem scan_freed (g : Graph α objects roots fields) (s : State objects roots fields)
    (fs : List (Fin fields)) : (scan g s fs).freed = s.freed := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    change (scan g (drop g s (.field f)) fs).freed = s.freed
    rw [ih, drop_freed]

theorem scan_weight (g : Graph α objects roots fields) (s : State objects roots fields)
    (fs : List (Fin fields)) : weight (scan g s fs) ≤ weight s := by
  induction fs generalizing s with
  | nil => exact Nat.le_refl _
  | cons f fs ih => exact Nat.le_trans (ih _) (drop_weight _ _ _)

theorem scan_own_subset (g : Graph α objects roots fields) (s : State objects roots fields)
    (fs : List (Fin fields)) : (scan g s fs).own ⊆ s.own := by
  induction fs generalizing s with
  | nil => exact List.Subset.refl _
  | cons f fs ih =>
    intro t ht
    exact List.mem_of_mem_erase (by simpa using ih _ ht)

theorem scan_field_absent (g : Graph α objects roots fields) (s : State objects roots fields)
    (hs : s.own.Nodup) {f : Fin fields} (fs : List (Fin fields)) (hf : f ∈ fs) :
    .field f ∉ (scan g s fs).own := by
  induction fs generalizing s with
  | nil => simp at hf
  | cons first fs ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · intro ht
      have hm := scan_own_subset g (drop g s (.field f)) fs ht
      exact hs.not_mem_erase (by simpa using hm)
    · exact ih _ (by simpa using hs.erase (.field first)) hf

/-- Pop, scan, and then reclaim a source, matching the native destructor order. -/
def visit (g : Graph α objects roots fields) (s : State objects roots fields)
    (o : Fin objects) : State objects roots fields :=
  let s' := scan g s (g.children o)
  { s' with freed := o :: s'.freed }

/-- Queued and reclaimed objects are distinct and have already lost their last reference. -/
def QueueSafe (s : State objects roots fields) : Prop :=
  (s.todo ++ s.freed).Nodup ∧ ∀ o ∈ s.todo ++ s.freed, s.rc o = none

theorem drop_queueSafe {g : Graph α objects roots fields} {s : State objects roots fields}
    {t : Token roots fields} (hq : QueueSafe s) : QueueSafe (drop g s t) := by
  have hn (hc : (s.rc (g.dst t)).isSome) : g.dst t ∉ s.todo ++ s.freed := by
    intro hm
    simp [hq.2 _ hm] at hc
  unfold drop
  split
  · dsimp only
    split
    · exact hq
    · rename_i rc hc
      have hn' := hn (by simp [hc])
      split <;> simp only [QueueSafe, List.cons_append, List.nodup_cons]
      · refine ⟨⟨hn', hq.1⟩, ?_⟩
        intro o ho
        simp only [List.mem_cons] at ho
        rcases ho with rfl | ho
        · simp [set]
        · have hne : o ≠ g.dst t := by intro h; subst o; exact hn' ho
          simp [set, hne, hq.2 _ ho]
      · refine ⟨hq.1, ?_⟩
        intro o ho
        have hne : o ≠ g.dst t := by intro h; subst o; exact hn' ho
        simp [set, hne, hq.2 _ ho]
  · exact hq

theorem drop_todo_mem_none {g : Graph α objects roots fields}
    {s : State objects roots fields} {o : Fin objects} (h : s.rc o = none)
    (t : Token roots fields) : o ∈ (drop g s t).todo ↔ o ∈ s.todo := by
  unfold drop
  split <;> (try dsimp only) <;> (try split) <;> (try split) <;> simp_all
  intro heq
  subst o
  simp_all

theorem scan_todo_mem_none {g : Graph α objects roots fields}
    {s : State objects roots fields} {o : Fin objects} (h : s.rc o = none)
    (fs : List (Fin fields)) : o ∈ (scan g s fs).todo ↔ o ∈ s.todo := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    exact (ih (drop_rc_none _ _ _ h)).trans (drop_todo_mem_none h _)

theorem scan_queueSafe {g : Graph α objects roots fields} {s : State objects roots fields}
    (hq : QueueSafe s) (fs : List (Fin fields)) : QueueSafe (scan g s fs) := by
  induction fs generalizing s with
  | nil => exact hq
  | cons f fs ih => exact ih (drop_queueSafe hq)

theorem pop_visit_safe {g : Graph α objects roots fields} {s : State objects roots fields}
    {o : Fin objects} {todo : List (Fin objects)} (h : s.todo = o :: todo)
    (hv : Valid g s) (hq : QueueSafe s) :
    Valid g (visit g { s with todo } o) ∧ QueueSafe (visit g { s with todo } o) := by
  have ho : s.rc o = none := hq.2 o (by simp [h])
  have hnodup : (o :: (todo ++ s.freed)).Nodup := by simpa [h] using hq.1
  have hn := (List.nodup_cons.mp hnodup).1
  have hq' : QueueSafe { s with todo } :=
    ⟨(List.nodup_cons.mp hnodup).2, fun p hp => hq.2 p (by simp_all)⟩
  have hs := scan_queueSafe (g := g) hq' (g.children o)
  have hnTodo : o ∉ (scan g { s with todo } (g.children o)).todo := by
    rw [scan_todo_mem_none (s := { s with todo }) ho]
    simp_all
  have hnFreed : o ∉ (scan g { s with todo } (g.children o)).freed := by
    simp_all
  have hsNone := scan_none (g := g) (s := { s with todo }) ho (g.children o)
  constructor
  · apply scan_valid (s := { s with todo }) hv
    intro f hf
    have hsource : g.source f = o := by simpa [Graph.children] using hf
    simpa [hsource] using ho
  · have hp := List.perm_middle (a := o)
      (l₁ := (scan g { s with todo } (g.children o)).todo)
      (l₂ := (scan g { s with todo } (g.children o)).freed)
    refine ⟨hp.nodup_iff.mpr ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨by simp_all, hs.1⟩
    · intro p hp
      simp only [visit, List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | hp
      · exact hs.2 _ (List.mem_append_left _ hp)
      · exact hsNone
      · exact hs.2 _ (List.mem_append_right _ hp)

/-- A total collector: there is no fuel parameter and no unproved termination assumption. -/
def drain (g : Graph α objects roots fields) (s : State objects roots fields) :
    State objects roots fields :=
  match _h : s.todo with
  | [] => s
  | o :: todo => drain g (visit g { s with todo } o)
termination_by weight s
decreasing_by
  have hw := scan_weight g { s with todo } (g.children o)
  simp only [visit, weight] at *
  simp only [_h, List.length_cons] at *
  omega

@[simp] theorem drain_todo (g : Graph α objects roots fields) (s : State objects roots fields) :
    (drain g s).todo = [] := by
  fun_induction drain g s with
  | case1 s h => exact h
  | case2 s o todo h ih => exact ih

/-- Reclaimed sources no longer own any outgoing reference. -/
def Complete (g : Graph α objects roots fields) (s : State objects roots fields) : Prop :=
  ∀ f, g.source f ∈ s.freed → .field f ∉ s.own

theorem drop_complete {g : Graph α objects roots fields} {s : State objects roots fields}
    (hc : Complete g s) (t : Token roots fields) : Complete g (drop g s t) := by
  intro f hf ht
  exact hc f (by simpa using hf) (List.mem_of_mem_erase (by simpa using ht))

@[simp] theorem drop_root_mem (g : Graph α objects roots fields)
    (s : State objects roots fields) (r : Fin roots) (f : Fin fields) :
    .root r ∈ (drop g s (.field f)).own ↔ .root r ∈ s.own := by
  simp

/-- Reachability uses the original graph, including fields not yet scanned by the collector. -/
inductive Reachable (g : Graph α objects roots fields) (r : Fin roots) : Fin objects → Prop
  | root : Reachable g r (g.root r)
  | field (f : Fin fields) : Reachable g r (g.source f) → Reachable g r (g.target f)

theorem reachable_live {g : Graph α objects roots fields} {s : State objects roots fields}
    (hv : Valid g s) {r : Fin roots} (hr : .root r ∈ s.own)
    {o : Fin objects} (hp : Reachable g r o) : (s.rc o).isSome := by
  induction hp with
  | root => exact token_live hv hr
  | field f hp ih => exact token_live hv (hv.2.1 f ih)

def observe (g : Graph α objects roots fields) (s : State objects roots fields)
    (o : Fin objects) : Option α :=
  if (s.rc o).isSome then some (g.payload o) else none

end RcGraph
