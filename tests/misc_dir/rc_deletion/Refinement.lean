import Heap
import Schedule

/-!
What the cascade of `Init/System/Deletion.lean` does on the ownership graph.

`collect_refines` shows that releasing a root through `collect`, which decides as `lean_dec_ref`
does and then runs the cascade on the heap of `Heap.lean`, ends in the state that `drain` computes,
so that `collect_released` gives it everything `Released` says; `cascade_refines` shows the same for
the cascade alone. The proof follows the code: the worklist is the chain of links the heap's cells
hold, and each release takes `drop`'s step on the counts.

`collect_safe` shows that on a valid heap the cascade records no fault: each count, link, slot and
terminal effect it touches is one that the heap's protocol allows at that point, so that nothing
is read after it is freed, no count is read after a link replaced it, and no object is freed before
its references are released or by another kind's terminal effect.
-/

namespace RcGraph

open Lean.Runtime.Deletion

variable {α : Type} {objects roots fields : Nat}

/-! ## The worklist a heap's links spell -/

/-- `Chain cell v L`: following links from `v` visits the queued objects `L` and ends at `NULL`. -/
inductive Chain (cell : Fin objects → Cell objects) : Val objects → List (Fin objects) → Prop
  | nil : Chain cell .null []
  | cons {o : Fin objects} {next : Val objects} {L : List (Fin objects)} :
      cell o = .queued next → Chain cell next L → Chain cell (.obj o) (o :: L)

theorem Chain.frame {cell cell' : Fin objects → Cell objects} {v : Val objects}
    {L : List (Fin objects)} (h : Chain cell v L) (hc : ∀ o ∈ L, cell' o = cell o) :
    Chain cell' v L := by
  induction h with
  | nil => exact .nil
  | cons hq _ ih =>
    exact .cons ((hc _ (by simp)).trans hq) (ih fun o ho => hc o (by simp [ho]))

theorem Chain.unique {cell : Fin objects → Cell objects} {v : Val objects}
    {L₁ L₂ : List (Fin objects)} (h₁ : Chain cell v L₁) (h₂ : Chain cell v L₂) : L₁ = L₂ := by
  induction h₁ generalizing L₂ with
  | nil => cases h₂; rfl
  | cons hq _ ih =>
    cases h₂ with
    | cons hq' h₂ =>
      rw [hq] at hq'
      cases hq'
      rw [ih h₂]

theorem Chain.queued {cell : Fin objects → Cell objects} {v : Val objects}
    {L : List (Fin objects)} (h : Chain cell v L) {o : Fin objects} (ho : o ∈ L) :
    ∃ next L', cell o = .queued next ∧ Chain cell next L' ∧ L'.length < L.length := by
  induction h with
  | nil => simp at ho
  | @cons p next L hq hn ih =>
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨next, L, hq, hn, by simp⟩
    · obtain ⟨n, L', h1, h2, h3⟩ := ih ho
      exact ⟨n, L', h1, h2, by simp; omega⟩

theorem Chain.nodup {cell : Fin objects → Cell objects} {v : Val objects}
    {L : List (Fin objects)} (h : Chain cell v L) : L.Nodup := by
  induction h with
  | nil => exact .nil
  | @cons o next L hq hn ih =>
    refine List.nodup_cons.mpr ⟨fun ho => ?_, ih⟩
    obtain ⟨n, L', h1, h2, h3⟩ := hn.queued ho
    rw [hq] at h1
    cases h1
    have := hn.unique h2
    subst this
    omega

theorem Chain.not_mem {cell : Fin objects → Cell objects} {v : Val objects}
    {L : List (Fin objects)} (h : Chain cell v L) {o : Fin objects}
    (ho : ∀ next, cell o ≠ .queued next) : o ∉ L := fun hm => by
  obtain ⟨n, _, h1, _⟩ := h.queued hm
  exact ho n h1

/-! ## Heap lemmas -/

@[simp] theorem Heap.check_own (h : Heap objects roots fields) (b : Bool) :
    (h.check b).own = h.own := by unfold Heap.check; split <;> rfl
@[simp] theorem Heap.check_cell (h : Heap objects roots fields) (b : Bool) :
    (h.check b).cell = h.cell := by unfold Heap.check; split <;> rfl
@[simp] theorem Heap.check_freed (h : Heap objects roots fields) (b : Bool) :
    (h.check b).freed = h.freed := by unfold Heap.check; split <;> rfl
@[simp] theorem Heap.check_state (h : Heap objects roots fields) (b : Bool)
    (L : List (Fin objects)) : (h.check b).state L = h.state L := by
  simp [Heap.state]
@[simp] theorem Heap.check_true (h : Heap objects roots fields) : h.check true = h := rfl
@[simp] theorem Heap.check_fault (h : Heap objects roots fields) (b : Bool) :
    (h.check b).fault = (h.fault || !b) := by
  unfold Heap.check; cases b <;> simp
@[simp] theorem Heap.setCell_fault (h : Heap objects roots fields) (o : Fin objects)
    (c : Cell objects) : (h.setCell o c).fault = h.fault := rfl
@[simp] theorem Heap.setCell_cell (h : Heap objects roots fields) (o : Fin objects)
    (c : Cell objects) (p : Fin objects) :
    (h.setCell o c).cell p = if p = o then c else h.cell p := rfl
@[simp] theorem Heap.setCell_own (h : Heap objects roots fields) (o : Fin objects)
    (c : Cell objects) : (h.setCell o c).own = h.own := rfl
@[simp] theorem Heap.setCell_freed (h : Heap objects roots fields) (o : Fin objects)
    (c : Cell objects) : (h.setCell o c).freed = h.freed := rfl
@[simp] theorem Heap.state_todo (h : Heap objects roots fields) (L : List (Fin objects)) :
    (h.state L).todo = L := rfl
@[simp] theorem Heap.state_rc (h : Heap objects roots fields) (L : List (Fin objects))
    (o : Fin objects) : (h.state L).rc o = (h.cell o).rc := rfl

theorem Heap.state_setCell (h : Heap objects roots fields) (o : Fin objects) (c : Cell objects)
    (L : List (Fin objects)) :
    (h.setCell o c).state L = { h.state L with rc := set (h.state L).rc o c.rc } := by
  simp only [Heap.state, Heap.setCell, State.mk.injEq, true_and, and_true]
  funext p
  simp only [set]
  split <;> rfl

theorem set_eq_self {rc : Fin objects → Option Int32} {o : Fin objects} {v : Option Int32}
    (h : rc o = v) : set rc o v = rc := by
  funext p
  simp only [set]
  split <;> simp_all

theorem Chain.setCell {h : Heap objects roots fields} {v : Val objects} {L : List (Fin objects)}
    (hch : Chain h.cell v L) {o : Fin objects} (ho : o ∉ L) (c : Cell objects) :
    Chain (h.setCell o c).cell v L :=
  hch.frame fun p hp => by
    have : p ≠ o := fun h => ho (h ▸ hp)
    simp [this]

/-! ## One release -/

attribute [ext] State

@[simp] theorem ofUInt32_one : Int32.ofUInt32 1 = 1 := by decide
@[simp] theorem ofUInt32_minus_one : Int32.ofUInt32 0xFFFFFFFF = -1 := by decide

theorem stickyDrop_eq : stickyDrop = LEAN_RC_STICKY_DROP.toUInt32 := by decide

/-- `decRef` with its tests in the order the cascade's `release` makes them. -/
theorem decRef_eq_cascade (rc : Int32) :
    decRef rc =
      if rc > 1 then some (rc - 1)
      else if rc == 1 then none
      else if rc.toUInt32 ≤ stickyDrop then some rc
      else if rc == -1 then none
      else some (rc + 1) := by
  rw [← decCascade_eq_decRef, stickyDrop_eq]

/-- The count step of `drop`, on a token already taken. -/
def countDrop (s : State objects roots fields) (p : Fin objects) : State objects roots fields :=
  match s.rc p with
  | none => s
  | some rc =>
    match decRef rc with
    | none => { s with rc := set s.rc p none, todo := p :: s.todo }
    | some rc' => { s with rc := set s.rc p (some rc') }

theorem drop_eq_countDrop (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) :
    drop g s t = if t ∈ s.own then countDrop { s with own := s.own.erase t } (g.dst t) else s := by
  unfold drop countDrop
  rfl

theorem zero_toUInt32_le : (0 : Int32).toUInt32 ≤ stickyDrop := by decide

theorem isLastShared_kept {m : Type → Type} [Monad m] {Obj Slot : Type} (A : Ops m Obj Slot)
    (o : Obj) {rc : Int32} (h : rc.toUInt32 ≤ stickyDrop) :
    isLastShared A o rc = pure false := by
  simp only [isLastShared, h, ↓reduceIte]

theorem isLastShared_atomic {m : Type → Type} [Monad m] {Obj Slot : Type} (A : Ops m Obj Slot)
    (o : Obj) {rc : Int32} (h : ¬ rc.toUInt32 ≤ stickyDrop) :
    isLastShared A o rc = A.releaseMt o >>= fun old => pure (old == -1) := by
  simp only [isLastShared, h, ↓reduceIte, ofUInt32_minus_one]

section Release

variable (g : Graph α objects roots fields) (l : Layout objects fields)
  (h : Heap objects roots fields) (p : Fin objects) (todo : Val objects)

theorem release_dead (hc : (h.cell p).rc = none) :
    (release (adapter g l) (.obj p) todo).run h = (todo, h.check false) := by
  have h0 := isLastShared_kept (adapter g l) (Val.obj p) zero_toUInt32_le
  cases hcp : h.cell p <;> simp_all [release, getRc, Cell.rc, StateT.run, bind, StateT.bind, pure,
    StateT.pure]

theorem release_many {rc : Int32} (hc : h.cell p = .live rc) (h1 : rc > 1) :
    (release (adapter g l) (.obj p) todo).run h = (todo, h.setCell p (.live (rc - 1))) := by
  have h1' : (rc == 1) = false := by
    simp only [beq_eq_false_iff_ne]; intro he; subst he; exact absurd h1 (by decide)
  simp [release, getRc, decRc, hc, h1, h1', StateT.run, bind, StateT.bind, pure, StateT.pure]

theorem release_one (hc : h.cell p = .live 1) :
    (release (adapter g l) (.obj p) todo).run h =
      (.obj p, ((h.setCell p .last).setCell p (.queued todo)).check
        (linkable (h.setCell p .last) todo)) := by
  simp [release, getRc, setNext, push, hc, StateT.run, bind, StateT.bind, pure, StateT.pure]

theorem release_kept {rc : Int32} (hc : h.cell p = .live rc) (h1 : ¬ rc > 1) (h2 : rc ≠ 1)
    (h3 : rc.toUInt32 ≤ stickyDrop) :
    (release (adapter g l) (.obj p) todo).run h = (todo, h) := by
  have h2' : (rc == 1) = false := by simpa using h2
  have hk := isLastShared_kept (adapter g l) (Val.obj p) h3
  simp [release, getRc, hc, h1, h2', hk, StateT.run, bind, StateT.bind, pure, StateT.pure]

theorem release_shared_last (hc : h.cell p = .live (-1)) :
    (release (adapter g l) (.obj p) todo).run h =
      (.obj p, ((h.setCell p .last).setCell p (.queued todo)).check
        (linkable (h.setCell p .last) todo)) := by
  have h3 : ¬ (-1 : Int32).toUInt32 ≤ stickyDrop := by decide
  have hk := isLastShared_atomic (adapter g l) (Val.obj p) h3
  have h1 : ¬ (-1 : Int32) > 1 := by decide
  have h2 : ((-1 : Int32) == 1) = false := by decide
  simp [release, getRc, releaseMt, setNext, push, hc, h1, h2, hk, StateT.run, bind, StateT.bind,
    pure, StateT.pure]

theorem release_shared {rc : Int32} (hc : h.cell p = .live rc) (h1 : ¬ rc > 1) (h2 : rc ≠ 1)
    (h3 : ¬ rc.toUInt32 ≤ stickyDrop) (h4 : rc ≠ -1) :
    (release (adapter g l) (.obj p) todo).run h =
      (todo, (h.setCell p (.live (rc + 1))).check (rc < 0)) := by
  have h2' : (rc == 1) = false := by simpa using h2
  have h4' : (rc == -1) = false := by simpa using h4
  have hk := isLastShared_atomic (adapter g l) (Val.obj p) h3
  simp [release, getRc, releaseMt, hc, h1, h2', h4', hk, StateT.run, bind, StateT.bind, pure,
    StateT.pure]

end Release

/-- Replacing the cell of `p` changes only its count; the worklist is given. -/
theorem state_replace {h h' : Heap objects roots fields} {L : List (Fin objects)} {p : Fin objects}
    (hown : h'.own = h.own) (hfreed : h'.freed = h.freed)
    (hcell : ∀ q, q ≠ p → h'.cell q = h.cell q) (L' : List (Fin objects)) (v : Option Int32)
    (hv : (h'.cell p).rc = v) :
    h'.state L' = { h.state L with rc := set (h.state L).rc p v, todo := L' } := by
  apply State.ext
  · simp [Heap.state, hown]
  · funext q
    simp only [Heap.state, set]
    by_cases hq : q = p
    · subst hq; simp [hv]
    · simp [hq, hcell q hq]
  · rfl
  · simp [Heap.state, hfreed]

/--
`release` on a pointer to `p` takes `drop`'s count step: the counter of `p` takes `decRef`,
and `p` is queued in front of the worklist if that was its last reference.
-/
theorem release_obj (g : Graph α objects roots fields) (l : Layout objects fields)
    (h : Heap objects roots fields) {L : List (Fin objects)} {todo : Val objects}
    (hch : Chain h.cell todo L) (p : Fin objects) :
    let r := (release (adapter g l) (.obj p) todo).run h
    r.2.state (countDrop (h.state L) p).todo = countDrop (h.state L) p ∧
      Chain r.2.cell r.1 (countDrop (h.state L) p).todo := by
  cases hc : h.cell p with
  | live rc =>
    have hpL : p ∉ L := hch.not_mem (by simp [hc])
    have hcd : countDrop (h.state L) p = match decRef rc with
        | none => { h.state L with rc := set (h.state L).rc p none, todo := p :: L }
        | some rc' => { h.state L with rc := set (h.state L).rc p (some rc') } := by
      simp [countDrop, hc, Cell.rc]
    have queue : ∀ {h' : Heap objects roots fields},
        (release (adapter g l) (.obj p) todo).run h = (.obj p, h') →
        (∀ q, q ≠ p → h'.cell q = h.cell q) → h'.own = h.own → h'.freed = h.freed →
        h'.cell p = .queued todo → decRef rc = none →
        let r := (release (adapter g l) (.obj p) todo).run h
        r.2.state (countDrop (h.state L) p).todo = countDrop (h.state L) p ∧
          Chain r.2.cell r.1 (countDrop (h.state L) p).todo := by
      intro h' hrun hq ho hf hp hd
      simp only [hcd, hd, hrun]
      refine ⟨state_replace ho hf hq _ _ (by simp [hp, Cell.rc]), .cons hp ?_⟩
      exact hch.frame fun q hqL => hq q fun e => hpL (e ▸ hqL)
    have keep : ∀ {h' : Heap objects roots fields} {rc' : Int32},
        (release (adapter g l) (.obj p) todo).run h = (todo, h') →
        (∀ q, q ≠ p → h'.cell q = h.cell q) → h'.own = h.own → h'.freed = h.freed →
        (h'.cell p).rc = some rc' → decRef rc = some rc' →
        let r := (release (adapter g l) (.obj p) todo).run h
        r.2.state (countDrop (h.state L) p).todo = countDrop (h.state L) p ∧
          Chain r.2.cell r.1 (countDrop (h.state L) p).todo := by
      intro h' rc' hrun hq ho hf hp hd
      simp only [hcd, hd, hrun]
      exact ⟨state_replace ho hf hq _ _ hp, hch.frame fun q hqL => hq q fun e => hpL (e ▸ hqL)⟩
    have hd := decRef_eq_cascade rc
    by_cases h1 : rc > 1
    · exact keep (rc' := rc - 1) (release_many g l h p todo hc h1) (fun q hq => by simp [hq]) rfl
        rfl (by simp [Cell.rc]) (by simp [hd, h1])
    · by_cases h2 : rc = 1
      · subst h2
        exact queue (release_one g l h p todo hc) (fun q hq => by simp [hq]) (by simp) (by simp)
          (by simp) (by simp [hd])
      · by_cases h3 : rc.toUInt32 ≤ stickyDrop
        · exact keep (rc' := rc) (release_kept g l h p todo hc h1 h2 h3) (fun _ _ => rfl) rfl rfl
            (by simp [hc, Cell.rc])
            (by rw [hd, ite_eq_right_of_eq_false _ _ (eq_false h1),
              ite_eq_right_of_eq_false _ _ (eq_false (by simpa using h2)),
              ite_eq_left_of_eq_true _ _ (eq_true h3)])
        · by_cases h4 : rc = -1
          · subst h4
            exact queue (release_shared_last g l h p todo hc) (fun q hq => by simp [hq])
              (by simp) (by simp) (by simp) (by decide)
          · exact keep (rc' := rc + 1) (release_shared g l h p todo hc h1 h2 h3 h4)
              (fun q hq => by simp [hq]) (by simp) (by simp) (by simp [Cell.rc])
              (by rw [hd, ite_eq_right_of_eq_false _ _ (eq_false h1),
                ite_eq_right_of_eq_false _ _ (eq_false (by simpa using h2)),
                ite_eq_right_of_eq_false _ _ (eq_false h3),
                ite_eq_right_of_eq_false _ _ (eq_false (by simpa using h4))])
  | _ =>
    have hcd : countDrop (h.state L) p = h.state L := by simp [countDrop, hc, Cell.rc]
    simp only [hcd, release_dead g l h p todo (by simp [hc, Cell.rc]), Heap.check_state,
      Heap.check_cell]
    exact ⟨rfl, hch⟩

/-! ## Slots -/

/-- `drop` of the reference a member holds, if it holds one. -/
def memberDrop (g : Graph α objects roots fields) (s : State objects roots fields) :
    Member fields → State objects roots fields
  | .field f => drop g s (.field f)
  | _ => s

theorem scan_eq_foldl (g : Graph α objects roots fields) (ms : List (Member fields)) :
    ∀ s, scan g s (ms.filterMap Member.field?) = ms.foldl (memberDrop g) s := by
  induction ms with
  | nil => intro s; rfl
  | cons m ms ih =>
    intro s
    cases m with
    | field f =>
      change scan g (drop g s (.field f)) (ms.filterMap Member.field?) = _
      exact ih _
    | scalar => exact ih s
    | null => exact ih s

theorem release_scalar (g : Graph α objects roots fields) (l : Layout objects fields)
    (h : Heap objects roots fields) (todo : Val objects) :
    (release (adapter g l) .scalar todo).run h = (todo, h) := rfl

theorem release_null (g : Graph α objects roots fields) (l : Layout objects fields)
    (h : Heap objects roots fields) (todo : Val objects) :
    (release (adapter g l) .null todo).run h = (todo, h.check false) := by
  have h0 := isLastShared_kept (adapter g l) (Val.null) zero_toUInt32_le
  simp [release, getRc, h0, StateT.run, bind, StateT.bind, pure, StateT.pure]

/-- Reading a member hands its reference to the release, which drops it. -/
theorem take_release (g : Graph α objects roots fields) (l : Layout objects fields)
    (h : Heap objects roots fields) {L : List (Fin objects)} {todo : Val objects}
    (hch : Chain h.cell todo L) (m : Member fields) :
    let r := (release (adapter g l) (take g h m).1 todo).run (take g h m).2
    r.2.state (memberDrop g (h.state L) m).todo = memberDrop g (h.state L) m ∧
      Chain r.2.cell r.1 (memberDrop g (h.state L) m).todo := by
  cases m with
  | field f =>
    by_cases ho : Token.field f ∈ h.own
    · have hd : memberDrop g (h.state L) (.field f) =
          countDrop ({ h with own := h.own.erase (.field f) }.state L) (g.target f) := by
        simp only [memberDrop, drop_eq_countDrop, Heap.state, ho, ↓reduceIte]
        rfl
      simp only [take, ho, ↓reduceIte, hd]
      exact release_obj g l { h with own := h.own.erase (.field f) } hch (g.target f)
    · have hd : memberDrop g (h.state L) (.field f) = h.state L := by
        simp only [memberDrop, drop_eq_countDrop, Heap.state, ho, ↓reduceIte]
      simp only [take, ho, ↓reduceIte, hd, release_scalar, Heap.check_state, Heap.check_cell]
      exact ⟨rfl, hch⟩
  | scalar => exact ⟨rfl, hch⟩
  | null =>
    simp only [take, release_null, Heap.check_state, Heap.check_cell, memberDrop]
    exact ⟨rfl, hch⟩

/-- A member read for a thunk or `Ref`, whose `NULL` the cascade skips before releasing. -/
theorem take_release_nonnull (g : Graph α objects roots fields) (l : Layout objects fields)
    (h : Heap objects roots fields) {L : List (Fin objects)} {todo : Val objects}
    (hch : Chain h.cell todo L) (m : Member fields) :
    let v := (take g h m).1
    let r := (if (adapter g l).isNull v then pure todo else release (adapter g l) v todo).run
      (take g h m).2
    r.2.state (memberDrop g (h.state L) m).todo = memberDrop g (h.state L) m ∧
      Chain r.2.cell r.1 (memberDrop g (h.state L) m).todo := by
  cases m with
  | null => exact ⟨rfl, hch⟩
  | field f =>
    have hv : ((take g h (.field f)).1 == Val.null) = false := by
      simp only [take]; split <;> rfl
    simp only [hv, Bool.false_eq_true, ↓reduceIte]
    exact take_release g l h hch _
  | scalar => exact ⟨rfl, hch⟩

theorem run_bind {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

theorem getSlot_run (g : Graph α objects roots fields) (l : Layout objects fields)
    (h : Heap objects roots fields) (o : Fin objects) (i : Nat) (m : Member fields)
    (hm : (l.members o)[i]? = some m) :
    ∃ b, ((adapter g l).getSlot (.obj o, i)).run h = take g (h.check b) m :=
  ⟨visiting l h o hasSlots && i < (l.members o).length && (l.members o)[i]? != some .null,
    by simp only [getSlot, hm, StateT.run]⟩

theorem member_run (g : Graph α objects roots fields) (l : Layout objects fields)
    (h : Heap objects roots fields) (tag : UInt8) (o : Fin objects) (i : Nat) (m : Member fields)
    (hm : (l.members o)[i]? = some m) :
    ∃ b, (member g l tag i (.obj o)).run h = take g (h.check b) m :=
  ⟨visiting l h o (· == tag) && i < (l.members o).length, by simp only [member, hm, StateT.run]⟩

theorem ofNat_zero : USize.ofNat 0 = 0 :=
  USize.toNat_inj.mp (by rw [USize.toNat_ofNat_of_lt' USize.size_pos, USize.toNat_zero])

theorem ofNat_ne_zero {n : Nat} (h : n + 1 < USize.size) : USize.ofNat (n + 1) ≠ 0 := by
  intro e
  have := congrArg USize.toNat e
  rw [USize.toNat_ofNat_of_lt' h, USize.toNat_zero] at this
  exact Nat.succ_ne_zero n this

theorem ofNat_sub_one {n : Nat} (h : n + 1 < USize.size) :
    USize.ofNat (n + 1) - 1 = USize.ofNat n := by
  have h1 : (1 : USize) ≤ USize.ofNat (n + 1) := by
    rw [USize.le_iff_toNat_le, USize.toNat_ofNat_of_lt' h, USize.toNat_one]; omega
  apply USize.toNat_inj.mp
  rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_ofNat_of_lt' h, USize.toNat_one,
    USize.toNat_ofNat_of_lt' (by omega)]
  omega

/-- `releaseSlots` from slot `i` of `o` drops the references of the remaining members. -/
theorem releaseSlots_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (o : Fin objects) :
    ∀ (n i : Nat) (h : Heap objects roots fields) (L : List (Fin objects)) (todo : Val objects),
      i + n = (l.members o).length → n < USize.size → Chain h.cell todo L →
      let r := (releaseSlots (adapter g l) (Val.obj o, i) (USize.ofNat n) todo).run h
      let s' := ((l.members o).drop i).foldl (memberDrop g) (h.state L)
      r.2.state s'.todo = s' ∧ Chain r.2.cell r.1 s'.todo := by
  intro n
  induction n with
  | zero =>
    intro i h L todo hi _ hch
    have : (l.members o).drop i = [] := List.drop_eq_nil_of_le (by omega)
    simp only [this, List.foldl_nil, Heap.state_todo]
    rw [releaseSlots, dite_eq_left ofNat_zero]
    exact ⟨rfl, hch⟩
  | succ n ih =>
    intro i h L todo hi hsz hch
    have hi' : i < (l.members o).length := by omega
    have hm : (l.members o)[i]? = some (l.members o)[i] := List.getElem?_eq_getElem hi'
    have hdrop : (l.members o).drop i = (l.members o)[i] :: (l.members o).drop (i + 1) :=
      List.drop_eq_getElem_cons hi'
    obtain ⟨b, hget⟩ := getSlot_run g l h o i _ hm
    have hstep := take_release g l (h.check b) (by simpa using hch) (l.members o)[i]
    simp only [Heap.check_state] at hstep
    generalize hr₁ : (release (adapter g l) (take g (h.check b) (l.members o)[i]).1 todo).run
      (take g (h.check b) (l.members o)[i]).2 = r₁ at hstep
    obtain ⟨todo₁, h₁⟩ := r₁
    have hrun : (releaseSlots (adapter g l) (Val.obj o, i) (USize.ofNat (n + 1)) todo).run h =
        (releaseSlots (adapter g l) (Val.obj o, i + 1) (USize.ofNat n) todo₁).run h₁ := by
      rw [releaseSlots, dite_eq_right (ofNat_ne_zero hsz), run_bind, hget, run_bind, hr₁,
        ofNat_sub_one hsz]
    have := ih (i + 1) h₁ _ todo₁ (by omega) (by omega) hstep.2
    rw [hrun, hdrop, List.foldl_cons, ← hstep.1]
    exact this

/-! ## Deleting one object -/

section Core

variable (g : Graph α objects roots fields) (l : Layout objects fields)

/-- What reading the kind leaves: the object is no longer counted, and nothing else changes. -/
theorem readTag_run (h : Heap objects roots fields) (o : Fin objects)
    (hdead : (h.cell o).rc = none) :
    ∃ h₁, ((adapter g l).tag (.obj o)).run h = (l.tag o, h₁) ∧ h₁.own = h.own ∧
      h₁.freed = h.freed ∧ (∀ q, q ≠ o → h₁.cell q = h.cell q) ∧ (h₁.cell o).rc = none := by
  cases hc : h.cell o with
  | live rc => simp [hc, Cell.rc] at hdead
  | last => exact ⟨h.setCell o .visited, by simp [readTag, hc, StateT.run], rfl, rfl,
      fun q hq => by simp [hq], by simp [Cell.rc]⟩
  | queued next => exact ⟨h.setCell o .visited, by simp [readTag, hc, StateT.run], rfl, rfl,
      fun q hq => by simp [hq], by simp [Cell.rc]⟩
  | visited => exact ⟨h.check false, by simp [readTag, hc, StateT.run], by simp, by simp,
      fun q _ => by simp, by simp [hc, Cell.rc]⟩
  | freed => exact ⟨h.check false, by simp [readTag, hc, StateT.run], by simp, by simp,
      fun q _ => by simp, by simp [hc, Cell.rc]⟩

/-- A terminal effect reclaims `o`, which is no longer counted. -/
theorem reclaim_refines (ok : UInt8 → Bool) (h : Heap objects roots fields)
    {L : List (Fin objects)} {todo : Val objects} (hch : Chain h.cell todo L) (o : Fin objects)
    (hoL : o ∉ L) (hdead : (h.cell o).rc = none) :
    let r := (reclaim l ok (.obj o)).run h
    r.2.state L = { h.state L with freed := o :: h.freed } ∧ Chain r.2.cell todo L := by
  refine ⟨?_, ?_⟩
  · apply State.ext
    · simp [reclaim, StateT.run, Heap.state]
    · funext q
      by_cases hq : q = o
      · subst hq; simp [reclaim, StateT.run, Heap.state, hdead]
      · simp [reclaim, StateT.run, Heap.state, hq]
    · rfl
    · simp [reclaim, StateT.run, Heap.state]
  · simpa [reclaim, StateT.run] using hch.setCell hoL .freed

/-- What remains of `visit` once the members of `o` are dropped: its reclamation. -/
theorem visit_eq (o : Fin objects) (hv : (l.members o).filterMap Member.field? = g.children o)
    (s : State objects roots fields) :
    visit g s o =
      let s' := (l.members o).foldl (memberDrop g) s
      { s' with freed := o :: s'.freed } := by
  simp only [visit, ← hv, scan_eq_foldl]

theorem foldl_memberDrop_none (ms : List (Member fields)) {o : Fin objects} :
    ∀ {s : State objects roots fields}, s.rc o = none →
      (ms.foldl (memberDrop g) s).rc o = none ∧
        (o ∈ (ms.foldl (memberDrop g) s).todo ↔ o ∈ s.todo) := by
  induction ms with
  | nil => intro s h; exact ⟨h, .rfl⟩
  | cons m ms ih =>
    intro s h
    cases m with
    | field f =>
      obtain ⟨h1, h2⟩ := ih (s := drop g s (.field f)) (drop_rc_none _ _ _ h)
      exact ⟨h1, h2.trans (drop_todo_mem_none h _)⟩
    | scalar => exact ih h
    | null => exact ih h

/-- Drop the members of `o` and then reclaim it, as `visit` does. -/
theorem finish_refines (ok : UInt8 → Bool) (h : Heap objects roots fields) {L : List (Fin objects)}
    (o : Fin objects) (hoL : o ∉ L) (hdead : (h.cell o).rc = none)
    (h₂ : Heap objects roots fields) (todo₂ : Val objects)
    (hstate : h₂.state ((l.members o).foldl (memberDrop g) (h.state L)).todo =
      (l.members o).foldl (memberDrop g) (h.state L))
    (hchain : Chain h₂.cell todo₂ ((l.members o).foldl (memberDrop g) (h.state L)).todo)
    (hv : (l.members o).filterMap Member.field? = g.children o) :
    let r := (do reclaim l ok (.obj o); pure todo₂ : M objects roots fields _).run h₂
    r.2.state (visit g (h.state L) o).todo = visit g (h.state L) o ∧
      Chain r.2.cell r.1 (visit g (h.state L) o).todo := by
  have hn := foldl_memberDrop_none g (l.members o) (s := h.state L) (by simpa using hdead)
  have hdead₂ : (h₂.cell o).rc = none := by
    have := congrArg (fun s => s.rc o) hstate
    simpa [hn.1] using this
  have hoL₂ : o ∉ ((l.members o).foldl (memberDrop g) (h.state L)).todo := by
    rw [hn.2]; simpa using hoL
  have hr := reclaim_refines l ok h₂ hchain o hoL₂ hdead₂
  rw [visit_eq g l o hv]
  simp only [run_bind] at hr ⊢
  refine ⟨?_, hr.2⟩
  rw [show (pure todo₂ : M objects roots fields _).run _ = (todo₂, _) from rfl]
  simp only
  rw [hr.1, hstate]
  have hf : h₂.freed = ((l.members o).foldl (memberDrop g) (h.state L)).freed :=
    congrArg State.freed hstate
  simp [hf]

theorem slots_run (ok : UInt8 → Bool) (h : Heap objects roots fields) (o : Fin objects) :
    ∃ b, (slots l ok (.obj o)).run h = ((.obj o, 0), h.check b) := ⟨_, rfl⟩

theorem numSlots_run (ok : UInt8 → Bool) (h : Heap objects roots fields) (o : Fin objects) :
    ∃ b, (numSlots l ok (.obj o)).run h = (USize.ofNat (l.members o).length, h.check b) :=
  ⟨_, rfl⟩

/-- A constructor, closure or array: release every slot, then reclaim. -/
theorem slotted_refines (ok ok' : UInt8 → Bool) (h : Heap objects roots fields)
    {L : List (Fin objects)} {todo : Val objects} (hch : Chain h.cell todo L) (o : Fin objects)
    (hoL : o ∉ L) (hdead : (h.cell o).rc = none)
    (hv : (l.members o).filterMap Member.field? = g.children o)
    (hsz : (l.members o).length < USize.size) :
    let r := (do
      let todo ← releaseSlots (adapter g l) (← slots l ok (.obj o)) (← numSlots l ok (.obj o)) todo
      reclaim l ok' (.obj o)
      return todo : M objects roots fields _).run h
    r.2.state (visit g (h.state L) o).todo = visit g (h.state L) o ∧
      Chain r.2.cell r.1 (visit g (h.state L) o).todo := by
  obtain ⟨b₁, hs⟩ := slots_run l ok h o
  obtain ⟨b₂, hn⟩ := numSlots_run l ok (h.check b₁) o
  have hrs := releaseSlots_refines g l o (l.members o).length 0 ((h.check b₁).check b₂) L todo
    (by simp) hsz (by simpa using hch)
  simp only [List.drop_zero, Heap.check_state] at hrs
  generalize hr : (releaseSlots (adapter g l) (Val.obj o, 0) (USize.ofNat (l.members o).length)
    todo).run ((h.check b₁).check b₂) = r at hrs
  obtain ⟨todo₂, h₂⟩ := r
  have := finish_refines g l ok' h o hoL hdead h₂ todo₂ hrs.1 hrs.2 hv
  simp only [run_bind, hs, hn, hr]
  exact this

/-- A thunk or `Ref`: release each member that is not `NULL`, then reclaim. -/
theorem members_refines (tag : UInt8) (ok : UInt8 → Bool) (h : Heap objects roots fields)
    {L : List (Fin objects)} {todo : Val objects} (hch : Chain h.cell todo L) (o : Fin objects)
    (hoL : o ∉ L) (hdead : (h.cell o).rc = none)
    (hv : (l.members o).filterMap Member.field? = g.children o) :
    (∀ m₀ m₁, l.members o = [m₀, m₁] →
      let r := (do
        let c ← member g l tag 0 (.obj o)
        let todo ← (if (adapter g l).isNull c then pure todo else release (adapter g l) c todo)
        let v ← member g l tag 1 (.obj o)
        let todo ← (if (adapter g l).isNull v then pure todo else release (adapter g l) v todo)
        reclaim l ok (.obj o)
        return todo : M objects roots fields _).run h
      r.2.state (visit g (h.state L) o).todo = visit g (h.state L) o ∧
        Chain r.2.cell r.1 (visit g (h.state L) o).todo) ∧
    (∀ m₀, l.members o = [m₀] →
      let r := (do
        let v ← member g l tag 0 (.obj o)
        let todo ← (if (adapter g l).isNull v then pure todo else release (adapter g l) v todo)
        reclaim l ok (.obj o)
        return todo : M objects roots fields _).run h
      r.2.state (visit g (h.state L) o).todo = visit g (h.state L) o ∧
        Chain r.2.cell r.1 (visit g (h.state L) o).todo) := by
  refine ⟨fun m₀ m₁ hms => ?_, fun m₀ hms => ?_⟩
  · obtain ⟨b₀, hm₀⟩ := member_run g l h tag o 0 m₀ (by simp [hms])
    have h₀ := take_release_nonnull g l (h.check b₀) (L := L) (todo := todo) (by simpa using hch) m₀
    simp only [Heap.check_state] at h₀
    generalize hr₀ : (if (adapter g l).isNull (take g (h.check b₀) m₀).1 then pure todo
      else release (adapter g l) (take g (h.check b₀) m₀).1 todo).run (take g (h.check b₀) m₀).2
      = r₀ at h₀
    obtain ⟨todo₀, h₀'⟩ := r₀
    obtain ⟨b₁, hm₁⟩ := member_run g l h₀' tag o 1 m₁ (by simp [hms])
    have h₁ := take_release_nonnull g l (h₀'.check b₁) (by simpa using h₀.2) m₁
    simp only [Heap.check_state, h₀.1] at h₁
    generalize hr₁ : (if (adapter g l).isNull (take g (h₀'.check b₁) m₁).1 then pure todo₀
      else release (adapter g l) (take g (h₀'.check b₁) m₁).1 todo₀).run
      (take g (h₀'.check b₁) m₁).2 = r₁ at h₁
    obtain ⟨todo₁, h₁'⟩ := r₁
    have hfin := finish_refines g l ok h o hoL hdead h₁' todo₁ (by simpa [hms] using h₁.1)
      (by simpa [hms] using h₁.2) hv
    simp only [run_bind, hm₀]
    rw [hr₀]
    simp only [hm₁]
    rw [hr₁]
    exact hfin
  · obtain ⟨b₀, hm₀⟩ := member_run g l h tag o 0 m₀ (by simp [hms])
    have h₀ := take_release_nonnull g l (h.check b₀) (L := L) (todo := todo) (by simpa using hch) m₀
    simp only [Heap.check_state] at h₀
    generalize hr₀ : (if (adapter g l).isNull (take g (h.check b₀) m₀).1 then pure todo
      else release (adapter g l) (take g (h.check b₀) m₀).1 todo).run (take g (h.check b₀) m₀).2
      = r₀ at h₀
    obtain ⟨todo₀, h₀'⟩ := r₀
    have hfin := finish_refines g l ok h o hoL hdead h₀' todo₀ (by simpa [hms] using h₀.1)
      (by simpa [hms] using h₀.2) hv
    simp only [run_bind, hm₀]
    rw [hr₀]
    exact hfin

/-- An object without members: reclaim it. -/
theorem leaf_refines (ok : UInt8 → Bool) (h : Heap objects roots fields) {L : List (Fin objects)}
    {todo : Val objects} (hch : Chain h.cell todo L) (o : Fin objects) (hoL : o ∉ L)
    (hdead : (h.cell o).rc = none) (hv : (l.members o).filterMap Member.field? = g.children o)
    (hms : l.members o = []) :
    let r := (do reclaim l ok (.obj o); return todo : M objects roots fields _).run h
    r.2.state (visit g (h.state L) o).todo = visit g (h.state L) o ∧
      Chain r.2.cell r.1 (visit g (h.state L) o).todo :=
  finish_refines g l ok h o hoL hdead h todo (by simp [hms]) (by simpa [hms] using hch) hv

theorem tag_cases (t : UInt8) (h0 : ¬ t ≤ LeanMaxCtorTag) (h1 : t ≠ LeanClosure)
    (h2 : t ≠ LeanArray) (h3 : t ≠ LeanScalarArray) (h4 : t ≠ LeanString) (h5 : t ≠ LeanMPZ)
    (h6 : t ≠ LeanThunk) (h7 : t ≠ LeanRef) (h8 : t ≠ LeanTask) (h9 : t ≠ LeanPromise)
    (h10 : t ≠ LeanExternal) : t = LeanStructArray ∨ t = LeanReserved := by
  have hl := t.toNat_lt
  simp only [UInt8.le_iff_toNat_le, ne_eq, ← UInt8.toNat_inj] at *
  simp only [LeanMaxCtorTag, LeanClosure, LeanArray, LeanScalarArray, LeanString, LeanMPZ,
    LeanThunk, LeanRef, LeanTask, LeanPromise, LeanExternal, LeanStructArray, LeanReserved,
    UInt8.reduceToNat] at *
  omega

/-- `core` deletes `o` as `visit` does. -/
theorem core_refines (hl : l.Valid g) (h : Heap objects roots fields) {L : List (Fin objects)}
    {todo : Val objects} (hch : Chain h.cell todo L) (o : Fin objects) (hoL : o ∉ L)
    (hdead : (h.cell o).rc = none) :
    let r := (core (adapter g l) (.obj o) todo).run h
    r.2.state (visit g (h.state L) o).todo = visit g (h.state L) o ∧
      Chain r.2.cell r.1 (visit g (h.state L) o).todo := by
  obtain ⟨h₁, hrun₁, hown₁, hfreed₁, hcell₁, hdead₁⟩ := readTag_run g l h o hdead
  have hch₁ : Chain h₁.cell todo L := hch.frame fun q hq => hcell₁ q fun e => hoL (e ▸ hq)
  have hst₁ : h₁.state L = h.state L := by
    apply State.ext
    · simp [Heap.state, hown₁]
    · funext q
      by_cases hq : q = o
      · subst hq; simp [Heap.state, hdead, hdead₁]
      · simp [Heap.state, hcell₁ q hq]
    · rfl
    · simp [Heap.state, hfreed₁]
  obtain ⟨hv, hshape, hsz⟩ := hl o
  rw [core, run_bind, hrun₁, ← hst₁]
  simp only
  by_cases hc : l.tag o ≤ LeanMaxCtorTag
  · simp only [hc, ↓reduceIte]
    exact slotted_refines g l _ _ h₁ hch₁ o hoL hdead₁ hv hsz
  simp only [hc, ↓reduceIte, coreOther]
  have yes {x : UInt8} (e : l.tag o = x) : (l.tag o == x) = true := by simp [e]
  have no {x : UInt8} (e : l.tag o ≠ x) : (l.tag o == x) = false := by simpa using e
  have hslots (h1 : l.tag o ≠ LeanClosure) (h2 : l.tag o ≠ LeanArray) :
      hasSlots (l.tag o) = false := by
    simp [hasSlots, hc, h1, h2]
  by_cases t1 : l.tag o = LeanClosure
  · simp only [yes t1, ↓reduceIte]
    exact slotted_refines g l _ _ h₁ hch₁ o hoL hdead₁ hv hsz
  simp only [no t1, Bool.false_eq_true, ↓reduceIte]
  by_cases t2 : l.tag o = LeanArray
  · simp only [yes t2, ↓reduceIte]
    exact slotted_refines g l _ _ h₁ hch₁ o hoL hdead₁ hv hsz
  simp only [no t2, Bool.false_eq_true, ↓reduceIte]
  have hshape' := hshape
  simp only [shapeOk, hslots t1 t2, Bool.false_eq_true, ↓reduceIte] at hshape'
  by_cases t6 : l.tag o = LeanThunk
  · simp only [yes t6, ↓reduceIte, beq_iff_eq] at hshape'
    obtain ⟨m₀, hms⟩ : ∃ m₀ m₁, l.members o = [m₀, m₁] := by
      match hm : l.members o, hshape' with
      | [m₀, m₁], _ => exact ⟨m₀, m₁, rfl⟩
    obtain ⟨m₁, hms⟩ := hms
    have t3 : l.tag o ≠ LeanScalarArray := by rw [t6]; decide
    have t4 : l.tag o ≠ LeanString := by rw [t6]; decide
    have t5 : l.tag o ≠ LeanMPZ := by rw [t6]; decide
    simp only [no t3, no t4, no t5, yes t6, Bool.false_eq_true, ↓reduceIte]
    exact (members_refines g l LeanThunk _ h₁ hch₁ o hoL hdead₁ hv).1 m₀ m₁ hms
  simp only [no t6, Bool.false_eq_true, ↓reduceIte] at hshape' ⊢
  by_cases t7 : l.tag o = LeanRef
  · simp only [yes t7, ↓reduceIte, beq_iff_eq] at hshape'
    obtain ⟨m₀, hms⟩ := List.length_eq_one_iff.mp hshape'
    have t3 : l.tag o ≠ LeanScalarArray := by rw [t7]; decide
    have t4 : l.tag o ≠ LeanString := by rw [t7]; decide
    have t5 : l.tag o ≠ LeanMPZ := by rw [t7]; decide
    simp only [no t3, no t4, no t5, yes t7, Bool.false_eq_true, ↓reduceIte]
    exact (members_refines g l LeanRef _ h₁ hch₁ o hoL hdead₁ hv).2 m₀ hms
  simp only [no t7, Bool.false_eq_true, ↓reduceIte] at hshape' ⊢
  by_cases t11 : l.tag o = LeanStructArray ∨ l.tag o = LeanReserved
  · exfalso
    rcases t11 with t11 | t11 <;> simp [yes t11] at hshape'
  have t11a : l.tag o ≠ LeanStructArray := fun e => t11 (.inl e)
  have t11b : l.tag o ≠ LeanReserved := fun e => t11 (.inr e)
  simp only [no t11a, no t11b, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    List.isEmpty_iff] at hshape'
  have leaf := fun ok => leaf_refines g l (todo := todo) ok h₁ hch₁ o hoL hdead₁ hv hshape'
  by_cases t3 : l.tag o = LeanScalarArray
  · simp only [yes t3, ↓reduceIte]; exact leaf _
  simp only [no t3, Bool.false_eq_true, ↓reduceIte]
  by_cases t4 : l.tag o = LeanString
  · simp only [yes t4, ↓reduceIte]; exact leaf _
  simp only [no t4, Bool.false_eq_true, ↓reduceIte]
  by_cases t5 : l.tag o = LeanMPZ
  · simp only [yes t5, ↓reduceIte]; exact leaf _
  simp only [no t5, Bool.false_eq_true, ↓reduceIte]
  by_cases t8 : l.tag o = LeanTask
  · simp only [yes t8, ↓reduceIte]; exact leaf _
  simp only [no t8, Bool.false_eq_true, ↓reduceIte]
  by_cases t9 : l.tag o = LeanPromise
  · simp only [yes t9, ↓reduceIte]; exact leaf _
  simp only [no t9, Bool.false_eq_true, ↓reduceIte]
  by_cases t10 : l.tag o = LeanExternal
  · simp only [yes t10, ↓reduceIte]; exact leaf _
  exact absurd (tag_cases _ hc t1 t2 t3 t4 t5 t6 t7 t8 t9 t10) t11

end Core

/-! ## The cascade -/

section Cascade

variable {m : Type → Type} [Monad m] [Lean.Order.MonadTail m] {Obj Slot : Type}

/-- The rest of an iteration of `cascadeLoop`: stop on an empty worklist, or pop it. -/
def resume (A : Ops m Obj Slot) (todo : Obj) : m Unit :=
  if A.isNull todo then pure () else A.getNext todo >>= cascadeLoop A todo

theorem cascadeLoop_eq (A : Ops m Obj Slot) (o todo : Obj) :
    cascadeLoop A o todo = core A o todo >>= resume A := by
  rw [cascadeLoop]
  rfl

end Cascade

theorem drain_nil (g : Graph α objects roots fields) {s : State objects roots fields}
    (hs : s.todo = []) : drain g s = s := by
  rw [drain]; split <;> simp_all

theorem drain_cons (g : Graph α objects roots fields) {s : State objects roots fields}
    {o : Fin objects} {rest : List (Fin objects)} (hs : s.todo = o :: rest) :
    drain g s = drain g (visit g { s with todo := rest } o) := by
  rw [drain]; split <;> simp_all

/-- `cascadeLoop`, once `core` returns, finishes as `drain` does. -/
theorem resume_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (hl : l.Valid g) (s : State objects roots fields) :
    ∀ (h : Heap objects roots fields) (todo : Val objects), Chain h.cell todo s.todo →
      h.state s.todo = s → ((resume (adapter g l) todo).run h).2.state [] = drain g s := by
  fun_induction drain g s with
  | case1 s hs =>
    intro h todo hch heq
    rw [hs] at hch heq
    cases hch
    exact heq
  | case2 s o rest hs ih =>
    intro h todo hch heq
    rw [hs] at hch heq
    cases hch with
    | @cons _ next _ hq hn =>
      have hoL : o ∉ rest := (List.nodup_cons.mp (Chain.cons hq hn).nodup).1
      have hcore := core_refines g l hl h hn o hoL (by simp [hq])
      have hst : h.state rest = { s with todo := rest } := by rw [← heq]; rfl
      rw [hst] at hcore
      have hrun : (resume (adapter g l) (.obj o)).run h =
          (resume (adapter g l) ((core (adapter g l) (.obj o) next).run h).1).run
            ((core (adapter g l) (.obj o) next).run h).2 := by
        have hnull : (Val.obj o == Val.null) = false := rfl
        have hget : ((adapter g l).getNext (.obj o)).run h = (next, h) := by
          simp [StateT.run, getNext, hq]
        conv => lhs; rw [resume]
        simp only [hnull, Bool.false_eq_true, ↓reduceIte]
        rw [run_bind, hget, cascadeLoop_eq, run_bind]
      rw [hrun]
      exact ih _ _ hcore.2 hcore.1

theorem ofState_state (s : State objects roots fields) : (Heap.ofState s).state s.todo = s := by
  apply State.ext
  · rfl
  · funext o; simp only [Heap.state, Heap.ofState]; cases s.rc o <;> rfl
  · rfl
  · rfl


/-- The cascade from an object this thread is responsible for finishes as `drain` does. -/
theorem cascade_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (hl : l.Valid g) (h : Heap objects roots fields) (p : Fin objects) (hp : h.cell p = .last)
    (s : State objects roots fields) (hs : s.todo = [p])
    (heq : h.state [] = { s with todo := [] }) :
    ((cascade (adapter g l) (.obj p)).run h).2.state [] = drain g s := by
  have hcore := core_refines g l hl h (L := []) .nil p (by simp) (by simp [hp])
  rw [heq] at hcore
  rw [drain_cons g hs, cascade, cascadeLoop_eq, run_bind]
  exact resume_refines g l hl _ _ _ hcore.2 hcore.1

/-! ## Releasing a root -/

/--
Releasing a root, deciding as `lean_dec_ref` does and deleting with the cascade, computes `drain`.
-/
theorem collect_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (hl : l.Valid g) (s : State objects roots fields) (hs : s.todo = []) (d : Fin roots) :
    collect g l s d = drain g (drop g s (.root d)) := by
  unfold collect decRoot
  by_cases ht : Token.root d ∈ s.own
  · simp only [ht, ↓reduceIte]
    have h₀ : (Heap.ofState { s with own := s.own.erase (.root d) }).state [] =
        { s with own := s.own.erase (.root d) } := by
      simpa [hs] using ofState_state { s with own := s.own.erase (.root d) }
    have hdrop := drop_eq_countDrop g s (.root d)
    simp only [ht, ↓reduceIte] at hdrop
    cases hrc : s.rc (g.root d) with
    | none =>
      simp only
      rw [hdrop, h₀, drain_nil g (by simp [countDrop, hrc, hs])]
      simp [countDrop, hrc]
    | some rc =>
      simp only
      cases hd : decRef rc with
      | some rc' =>
        simp only
        rw [hdrop, drain_nil g (by simp [countDrop, hrc, hd, hs]), Heap.state_setCell, h₀]
        simp [countDrop, hrc, hd, Graph.dst]
      | none =>
        simp only
        rw [hdrop]
        apply cascade_refines g l hl _ (g.root d) (by simp)
        · simp [countDrop, hrc, hd, hs]
        · rw [Heap.state_setCell, h₀]
          simp [countDrop, hrc, hd, hs]
  · simp only [ht, ↓reduceIte]
    rw [drop_of_not_mem g ht, drain_nil g hs]
    simpa [hs] using ofState_state s

/--
Releasing root `d` through the cascade does what `Released` says, and every other schedule run until
no step applies ends in the same state, up to the order of reclamation.
-/
theorem collect_released {g : Graph α objects roots fields} (l : Layout objects fields)
    (hl : l.Valid g) {s : State objects roots fields} (hs : Quiescent g s) (d : Fin roots) :
    Released g s d (collect g l s d) ∧
      ∀ a, Steps g (drop g s (.root d)) a → Stuck g a → Equiv a (collect g l s d) := by
  rw [collect_refines g l hl s hs.todo]
  exact drain_released hs d

/-! ## The access protocol -/

section Protocol

variable (g : Graph α objects roots fields) (l : Layout objects fields)

theorem Chain.linkable {h : Heap objects roots fields} {todo : Val objects}
    {L : List (Fin objects)} (hch : Chain h.cell todo L) : linkable h todo = true := by
  cases hch with
  | nil => rfl
  | @cons o next _ hq _ =>
    show (match h.cell o with | .queued _ => true | _ => false) = true
    rw [hq]

/--
A release on a live object keeps the protocol, changes only that object's cell, and leaves
ownership alone.
-/
theorem release_obj_safe (h : Heap objects roots fields) {L : List (Fin objects)}
    {todo : Val objects} (hch : Chain h.cell todo L) (p : Fin objects) {rc : Int32}
    (hp : h.cell p = .live rc) :
    let r := (release (adapter g l) (.obj p) todo).run h
    r.2.fault = h.fault ∧ r.2.own = h.own ∧ ∀ q, q ≠ p → r.2.cell q = h.cell q := by
  have hpL : p ∉ L := hch.not_mem (by simp [hp])
  have hlink : linkable (h.setCell p .last) todo = true :=
    (hch.setCell hpL .last).linkable
  dsimp only
  by_cases h1 : rc > 1
  · rw [release_many g l h p todo hp h1]
    exact ⟨by simp, by simp, fun q hq => by simp [hq]⟩
  · by_cases h2 : rc = 1
    · subst h2
      rw [release_one g l h p todo hp]
      exact ⟨by simp [hlink], by simp, fun q hq => by simp [hq]⟩
    · by_cases h3 : rc.toUInt32 ≤ stickyDrop
      · rw [release_kept g l h p todo hp h1 h2 h3]
        exact ⟨rfl, rfl, fun _ _ => rfl⟩
      · by_cases h4 : rc = -1
        · subst h4
          rw [release_shared_last g l h p todo hp]
          exact ⟨by simp [hlink], by simp, fun q hq => by simp [hq]⟩
        · have hneg : rc < 0 := by
            have := (not_congr (RcCounts.stickyDrop_unsigned rc)).mp (stickyDrop_eq ▸ h3)
            simp only [Int32.lt_iff_toInt_lt, Int32.toInt_zero]
            omega
          rw [release_shared g l h p todo hp h1 h2 h3 h4]
          exact ⟨by simp [hneg], by simp, fun q hq => by simp [hq]⟩

/-- The tokens left once a member's reference is taken. -/
def takeOwn (own : Ownership roots fields) : Member fields → Ownership roots fields
  | .field f => own.erase (.field f)
  | _ => own

/-- Reading a member and releasing what it holds keeps the protocol when its reference is owned. -/
theorem take_release_safe (h : Heap objects roots fields) {L : List (Fin objects)}
    {todo : Val objects} (hch : Chain h.cell todo L) (hv : Valid g (h.state L))
    (m : Member fields) (hm : ∀ f, m = .field f → Token.field f ∈ h.own) (hnull : m ≠ .null) :
    let r := (release (adapter g l) (take g h m).1 todo).run (take g h m).2
    r.2.fault = h.fault ∧ (∀ q, (∀ rc, h.cell q ≠ .live rc) → r.2.cell q = h.cell q) ∧
      r.2.own = takeOwn h.own m := by
  cases m with
  | field f =>
    have ho := hm f rfl
    have hlive := token_live hv (t := .field f) ho
    obtain ⟨rc, hrc⟩ : ∃ rc, h.cell (g.target f) = .live rc := by
      revert hlive
      simp only [Heap.state_rc, Graph.dst_field]
      cases h.cell (g.target f) <;> simp
    simp only [take, ho, ↓reduceIte]
    obtain ⟨hf, hown, hcell⟩ := release_obj_safe g l { h with own := h.own.erase (.field f) } hch
      (g.target f) hrc
    refine ⟨hf, fun q hq => ?_, hown⟩
    exact hcell q (fun e => by subst e; exact hq rc hrc)
  | scalar => exact ⟨rfl, fun _ _ => rfl, rfl⟩
  | null => exact absurd rfl hnull

/-- The same for a thunk or `Ref` member, whose `NULL` is skipped. -/
theorem take_release_nonnull_safe (h : Heap objects roots fields) {L : List (Fin objects)}
    {todo : Val objects} (hch : Chain h.cell todo L) (hv : Valid g (h.state L))
    (m : Member fields) (hm : ∀ f, m = .field f → Token.field f ∈ h.own) :
    let v := (take g h m).1
    let r := (if (adapter g l).isNull v then pure todo else release (adapter g l) v todo).run
      (take g h m).2
    r.2.fault = h.fault ∧ (∀ q, (∀ rc, h.cell q ≠ .live rc) → r.2.cell q = h.cell q) ∧
      r.2.own = takeOwn h.own m := by
  cases m with
  | null => exact ⟨rfl, fun _ _ => rfl, rfl⟩
  | field f =>
    have hv' : ((take g h (.field f)).1 == Val.null) = false := by
      simp only [take, hm f rfl, ↓reduceIte]; rfl
    simp only [hv', Bool.false_eq_true, ↓reduceIte]
    exact take_release_safe g l h hch hv _ hm (by simp)
  | scalar => exact ⟨rfl, fun _ _ => rfl, rfl⟩

/-- The field occurrences an object's members hold are its own, each once. -/
theorem members_fields (hl : l.Valid g) (o : Fin objects) :
    ((l.members o).filterMap Member.field?).Nodup ∧
      ∀ f, Member.field f ∈ l.members o → g.source f = o := by
  rw [(hl o).1]
  refine ⟨(List.nodup_finRange fields).filter _, fun f hf => ?_⟩
  have : f ∈ (l.members o).filterMap Member.field? := List.mem_filterMap.mpr ⟨_, hf, rfl⟩
  rw [(hl o).1] at this
  simpa [Graph.children] using this

/--
`releaseSlots` from slot `i` of an object being deleted keeps the protocol when each
remaining slot holds an owned reference or an immediate, and releases all of those references.
-/
theorem releaseSlots_safe (hl : l.Valid g) (o : Fin objects) (hslots : hasSlots (l.tag o) = true)
    (hnull : Member.null ∉ l.members o) :
    ∀ (n i : Nat) (h : Heap objects roots fields) (L : List (Fin objects)) (todo : Val objects),
      i + n = (l.members o).length → n < USize.size → Chain h.cell todo L →
      h.cell o = .visited → Valid g (h.state L) →
      (∀ f, Member.field f ∈ (l.members o).drop i → Token.field f ∈ h.own) →
      let r := (releaseSlots (adapter g l) (Val.obj o, i) (USize.ofNat n) todo).run h
      r.2.fault = h.fault ∧ r.2.cell o = .visited ∧ r.2.own.Sublist h.own ∧
        ∀ f, Member.field f ∈ (l.members o).drop i → Token.field f ∉ r.2.own := by
  obtain ⟨hnd, hsrc⟩ := members_fields g l hl o
  intro n
  induction n with
  | zero =>
    intro i h L todo hi _ hch hvis hv hown
    have : (l.members o).drop i = [] := List.drop_eq_nil_of_le (by omega)
    simp only [this, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    rw [releaseSlots, dite_eq_left ofNat_zero]
    exact ⟨rfl, hvis, List.Sublist.refl _⟩
  | succ n ih =>
    intro i h L todo hi hsz hch hvis hv hown
    have hi' : i < (l.members o).length := by omega
    have hm : (l.members o)[i]? = some (l.members o)[i] := List.getElem?_eq_getElem hi'
    have hdrop : (l.members o).drop i = (l.members o)[i] :: (l.members o).drop (i + 1) :=
      List.drop_eq_getElem_cons hi'
    have hmnull : (l.members o)[i] ≠ .null := fun e =>
      hnull (e ▸ List.getElem_mem hi')
    have hcheck : (visiting l h o hasSlots && decide (i < (l.members o).length) &&
        (l.members o)[i]? != some .null) = true := by
      simp [visiting, hvis, hslots, hi', hmnull]
    have hget : ((adapter g l).getSlot (.obj o, i)).run h = take g h (l.members o)[i] := by
      simp only [StateT.run]
      show (let h' := h.check _; match (l.members o)[i]? with
        | some m => take g h' m | none => (.scalar, h')) = _
      rw [hcheck, Heap.check_true, hm]
    have hown_i : ∀ f, (l.members o)[i] = .field f → Token.field f ∈ h.own :=
      fun f e => hown f (by rw [hdrop, e]; simp)
    have hsafe := take_release_safe g l h hch hv (l.members o)[i] hown_i hmnull
    have hstep := take_release g l h hch (l.members o)[i]
    generalize hr₁ : (release (adapter g l) (take g h (l.members o)[i]).1 todo).run
      (take g h (l.members o)[i]).2 = r₁ at hsafe hstep
    obtain ⟨todo₁, h₁⟩ := r₁
    have hrun : (releaseSlots (adapter g l) (Val.obj o, i) (USize.ofNat (n + 1)) todo).run h =
        (releaseSlots (adapter g l) (Val.obj o, i + 1) (USize.ofNat n) todo₁).run h₁ := by
      rw [releaseSlots, dite_eq_right (ofNat_ne_zero hsz), run_bind, hget, run_bind, hr₁,
        ofNat_sub_one hsz]
    obtain ⟨hf₁, hcell₁, hown₁⟩ := hsafe
    have hvis₁ : h₁.cell o = .visited := by rw [hcell₁ o (by simp [hvis])]; exact hvis
    have hnodup : h.own.Nodup := hv.1
    -- The state after this slot is `drop`'s, which stays valid: the slot's object is dead.
    have hv₁ : Valid g (h₁.state (memberDrop g (h.state L) (l.members o)[i]).todo) := by
      rw [hstep.1]
      cases hmi : (l.members o)[i] with
      | field f =>
        have hs : g.source f = o := hsrc f (hmi ▸ List.getElem_mem hi')
        exact drop_valid hv (by simp [Droppable, hs, hvis])
      | scalar => exact hv
      | null => exact absurd hmi hmnull
    have hrest : ((l.members o).drop i).filterMap Member.field? =
        ((l.members o)[i]).field?.toList ++
          ((l.members o).drop (i + 1)).filterMap Member.field? := by
      rw [hdrop]; cases (l.members o)[i] <;> rfl
    have hnd_i : (((l.members o).drop i).filterMap Member.field?).Nodup :=
      (List.drop_sublist _ _).filterMap _ |>.nodup hnd
    have hown₁' : ∀ f, Member.field f ∈ (l.members o).drop (i + 1) → Token.field f ∈ h₁.own := by
      intro f hf
      rw [hown₁]
      have hf0 := hown f (by rw [hdrop]; exact List.mem_cons_of_mem _ hf)
      cases hmi : (l.members o)[i] with
      | field f₀ =>
        refine (List.mem_erase_of_ne ?_).mpr hf0
        intro e
        cases e
        rw [hrest, hmi] at hnd_i
        have : f ∈ ((l.members o).drop (i + 1)).filterMap Member.field? :=
          List.mem_filterMap.mpr ⟨_, hf, rfl⟩
        exact (List.nodup_cons.mp hnd_i).1 this
      | scalar => exact hf0
      | null => exact absurd hmi hmnull
    obtain ⟨hf₂, hvis₂, hsub₂, habs₂⟩ :=
      ih (i + 1) h₁ _ todo₁ (by omega) (by omega) hstep.2 hvis₁ hv₁ hown₁'
    rw [hrun]
    refine ⟨hf₂.trans hf₁, hvis₂, hsub₂.trans ?_, ?_⟩
    · rw [hown₁]; cases (l.members o)[i] <;> first | exact List.erase_sublist | exact .refl _
    · intro f hf
      rw [hdrop] at hf
      rcases List.mem_cons.mp hf with e | hf
      · intro hmem
        have hgone : Token.field f ∉ h₁.own := by
          rw [hown₁, ← e]
          exact hnodup.not_mem_erase
        exact hgone (hsub₂.subset hmem)
      · exact habs₂ f hf

/-- A terminal effect keeps the protocol on a visited object of its kind with no references left. -/
theorem reclaim_safe (ok : UInt8 → Bool) (h : Heap objects roots fields) (o : Fin objects)
    (hvis : h.cell o = .visited) (hok : ok (l.tag o) = true)
    (hrel : ∀ f, Member.field f ∈ l.members o → Token.field f ∉ h.own) :
    ((reclaim l ok (.obj o)).run h).2.fault = h.fault := by
  have hr : released l h o = true := by
    simp only [released, List.all_eq_true]
    intro m hm
    cases m with
    | field f => simpa using hrel f hm
    | scalar => rfl
    | null => rfl
  simp [reclaim, StateT.run, visiting, hvis, hok, hr]

theorem takeOwn_sublist (own : Ownership roots fields) (m : Member fields) :
    (takeOwn own m).Sublist own := by
  cases m <;> first | exact List.erase_sublist | exact .refl _

theorem takeOwn_mem {own : Ownership roots fields} {m : Member fields} {f : Fin fields}
    (hf : Token.field f ∈ own) (hne : m ≠ .field f) : Token.field f ∈ takeOwn own m := by
  cases m with
  | field f₀ => exact (List.mem_erase_of_ne (fun e => hne (by cases e; rfl))).mpr hf
  | scalar => exact hf
  | null => exact hf

theorem takeOwn_not_mem {own : Ownership roots fields} (hnd : own.Nodup) (f : Fin fields) :
    Token.field f ∉ takeOwn own (.field f) :=
  hnd.not_mem_erase

/-- A thunk's two members, or a `Ref`'s one, then the terminal effect, keep the protocol. -/
theorem members_safe (hl : l.Valid g) (o : Fin objects) (tag : UInt8) (ok : UInt8 → Bool)
    (hok : ok (l.tag o) = true) (htag : l.tag o = tag) (h : Heap objects roots fields)
    {L : List (Fin objects)} {todo : Val objects} (hch : Chain h.cell todo L)
    (hvis : h.cell o = .visited)
    (hv : Valid g (h.state L)) (hown : ∀ f, Member.field f ∈ l.members o → Token.field f ∈ h.own) :
    (∀ m₀ m₁, l.members o = [m₀, m₁] →
      let r := (do
        let c ← member g l tag 0 (.obj o)
        let todo ← (if (adapter g l).isNull c then pure todo else release (adapter g l) c todo)
        let v ← member g l tag 1 (.obj o)
        let todo ← (if (adapter g l).isNull v then pure todo else release (adapter g l) v todo)
        reclaim l ok (.obj o)
        return todo : M objects roots fields _).run h
      r.2.fault = h.fault) ∧
    (∀ m₀, l.members o = [m₀] →
      let r := (do
        let v ← member g l tag 0 (.obj o)
        let todo ← (if (adapter g l).isNull v then pure todo else release (adapter g l) v todo)
        reclaim l ok (.obj o)
        return todo : M objects roots fields _).run h
      r.2.fault = h.fault) := by
  obtain ⟨hnd, hsrc⟩ := members_fields g l hl o
  have hvis' : ∀ {h' : Heap objects roots fields}, (∀ q, (∀ rc, h.cell q ≠ .live rc) →
      h'.cell q = h.cell q) → h'.cell o = .visited := fun hc => by
    rw [hc o (by simp [hvis])]; exact hvis
  have hdead : (h.state L).rc o = none := by simp [hvis]
  have hvisit : ∀ {h' : Heap objects roots fields}, h'.cell o = .visited →
      visiting l h' o (· == tag) = true := fun e => by simp [visiting, e, htag]
  refine ⟨fun m₀ m₁ hms => ?_, fun m₀ hms => ?_⟩
  · have hm₀ : (member g l tag 0 (.obj o)).run h = take g h m₀ := by
      simp [member, StateT.run, hms, hvisit hvis]
    have hs₀ := take_release_nonnull_safe g l h hch hv m₀
      (fun f e => hown f (by simp [hms, e]))
    have hr₀ := take_release_nonnull g l h (todo := todo) hch m₀
    dsimp only at hs₀ hr₀
    generalize hx₀ : (if (adapter g l).isNull (take g h m₀).1 then pure todo
      else release (adapter g l) (take g h m₀).1 todo).run (take g h m₀).2 = x₀ at hs₀ hr₀
    obtain ⟨todo₀, h₀⟩ := x₀
    obtain ⟨hf₀, hc₀, ho₀⟩ := hs₀
    have hvis₀ : h₀.cell o = .visited := hvis' hc₀
    have hv₀ : Valid g (h₀.state (memberDrop g (h.state L) m₀).todo) := by
      rw [hr₀.1]
      cases m₀ with
      | field f => exact drop_valid hv (by simp [Droppable, hsrc f (by simp [hms]), hvis])
      | _ => exact hv
    have hown₀ : ∀ f, m₁ = .field f → Token.field f ∈ h₀.own := by
      intro f e
      rw [ho₀]
      refine takeOwn_mem (hown f (by simp [hms, e])) fun e₀ => ?_
      subst e e₀
      rw [hms] at hnd
      simp [Member.field?] at hnd
    have hm₁ : (member g l tag 1 (.obj o)).run h₀ = take g h₀ m₁ := by
      simp [member, StateT.run, hms, hvisit hvis₀]
    have hs₁ := take_release_nonnull_safe g l h₀ hr₀.2 hv₀ m₁ hown₀
    dsimp only at hs₁
    generalize hx₁ : (if (adapter g l).isNull (take g h₀ m₁).1 then pure todo₀
      else release (adapter g l) (take g h₀ m₁).1 todo₀).run (take g h₀ m₁).2 = x₁ at hs₁
    obtain ⟨todo₁, h₁⟩ := x₁
    obtain ⟨hf₁, hc₁, ho₁⟩ := hs₁
    have hvis₁ : h₁.cell o = .visited := by rw [hc₁ o (by simp [hvis₀])]; exact hvis₀
    have hrel : ∀ f, Member.field f ∈ l.members o → Token.field f ∉ h₁.own := by
      intro f hf
      rw [hms] at hf
      rw [ho₁, ho₀]
      have hnd₀ : h.own.Nodup := hv.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with e | e
      · subst e
        exact fun hm => takeOwn_not_mem hnd₀ f ((takeOwn_sublist _ _).subset hm)
      · subst e
        exact takeOwn_not_mem ((takeOwn_sublist _ _).nodup hnd₀) f
    have hfin := reclaim_safe l ok h₁ o hvis₁ hok hrel
    simp only [run_bind, hm₀]
    rw [hx₀]
    simp only [hm₁]
    rw [hx₁]
    simp only
    have hp : ∀ x, ((pure todo₁ : M objects roots fields _).run x).2 = x := fun _ => rfl
    rw [hp, hfin, hf₁, hf₀]
  · have hm₀ : (member g l tag 0 (.obj o)).run h = take g h m₀ := by
      simp [member, StateT.run, hms, hvisit hvis]
    have hs₀ := take_release_nonnull_safe g l h hch hv m₀
      (fun f e => hown f (by simp [hms, e]))
    dsimp only at hs₀
    generalize hx₀ : (if (adapter g l).isNull (take g h m₀).1 then pure todo
      else release (adapter g l) (take g h m₀).1 todo).run (take g h m₀).2 = x₀ at hs₀
    obtain ⟨todo₀, h₀⟩ := x₀
    obtain ⟨hf₀, hc₀, ho₀⟩ := hs₀
    have hvis₀ : h₀.cell o = .visited := hvis' hc₀
    have hrel : ∀ f, Member.field f ∈ l.members o → Token.field f ∉ h₀.own := by
      intro f hf
      rw [hms, List.mem_singleton] at hf
      subst hf
      rw [ho₀]
      exact takeOwn_not_mem hv.1 f
    have hfin := reclaim_safe l ok h₀ o hvis₀ hok hrel
    simp only [run_bind, hm₀]
    rw [hx₀]
    simp only
    have hp : ∀ x, ((pure todo₀ : M objects roots fields _).run x).2 = x := fun _ => rfl
    rw [hp, hfin, hf₀]

/-- A constructor, closure or array, released slot by slot and reclaimed, keeps the protocol. -/
theorem slotted_safe (hl : l.Valid g) (o : Fin objects) (ok ok' : UInt8 → Bool)
    (hok : ok (l.tag o) = true) (hok' : ok' (l.tag o) = true) (hslots : hasSlots (l.tag o) = true)
    (hnull : Member.null ∉ l.members o) (hsz : (l.members o).length < USize.size)
    (h : Heap objects roots fields) {L : List (Fin objects)}
    {todo : Val objects} (hch : Chain h.cell todo L) (hvis : h.cell o = .visited)
    (hv : Valid g (h.state L)) (hown : ∀ f, Member.field f ∈ l.members o → Token.field f ∈ h.own) :
    let r := (do
      let todo ← releaseSlots (adapter g l) (← slots l ok (.obj o)) (← numSlots l ok (.obj o)) todo
      reclaim l ok' (.obj o)
      return todo : M objects roots fields _).run h
    r.2.fault = h.fault := by
  have hvisit : visiting l h o ok = true := by simp [visiting, hvis, hok]
  have hs : (slots l ok (.obj o)).run h = ((.obj o, 0), h) := by
    simp [slots, StateT.run, hvisit]
  have hn : (numSlots l ok (.obj o)).run h = (USize.ofNat (l.members o).length, h) := by
    simp [numSlots, StateT.run, hvisit]
  have hrs := releaseSlots_safe g l hl o hslots hnull (l.members o).length 0 h L todo (by simp)
    hsz hch hvis hv (by simpa using hown)
  simp only [List.drop_zero] at hrs
  generalize hr : (releaseSlots (adapter g l) (Val.obj o, 0) (USize.ofNat (l.members o).length)
    todo).run h = r at hrs
  obtain ⟨todo₂, h₂⟩ := r
  obtain ⟨hf₂, hvis₂, -, habs₂⟩ := hrs
  have hfin := reclaim_safe l ok' h₂ o hvis₂ hok' habs₂
  simp only [run_bind, hs, hn, hr]
  have hp : ∀ x, ((pure todo₂ : M objects roots fields _).run x).2 = x := fun _ => rfl
  rw [hp, hfin, hf₂]

/--
`core` keeps the protocol on an object this thread is responsible for whose references
are all owned: each count, link, slot and terminal effect it touches is one the protocol allows.
-/
theorem core_safe (hl : l.Valid g) (h : Heap objects roots fields) {L : List (Fin objects)}
    {todo : Val objects} (hch : Chain h.cell todo L) (o : Fin objects) (hoL : o ∉ L)
    (hcell : h.cell o = .last ∨ ∃ n, h.cell o = .queued n) (hv : Valid g (h.state L))
    (hown : ∀ f, Member.field f ∈ l.members o → Token.field f ∈ h.own) :
    ((core (adapter g l) (.obj o) todo).run h).2.fault = h.fault := by
  have hrun₁ : ((adapter g l).tag (.obj o)).run h = (l.tag o, h.setCell o .visited) := by
    rcases hcell with e | ⟨n, e⟩ <;> simp [readTag, StateT.run, e]
  have hdead : (h.cell o).rc = none := by rcases hcell with e | ⟨n, e⟩ <;> simp [e]
  have hch₁ : Chain (h.setCell o .visited).cell todo L := hch.setCell hoL _
  have hst₁ : (h.setCell o .visited).state L = h.state L := by
    apply State.ext
    · rfl
    · funext q
      by_cases hq : q = o
      · subst hq; simp [Heap.state, hdead]
      · simp [Heap.state, hq]
    · rfl
    · rfl
  have hv₁ : Valid g ((h.setCell o .visited).state L) := by rw [hst₁]; exact hv
  have hvis₁ : (h.setCell o .visited).cell o = .visited := by simp
  have hown₁ : ∀ f, Member.field f ∈ l.members o → Token.field f ∈ (h.setCell o .visited).own :=
    hown
  obtain ⟨-, hshape, hsz⟩ := hl o
  rw [core, run_bind, hrun₁]
  simp only
  rw [show h.fault = (h.setCell o .visited).fault from rfl]
  generalize h.setCell o .visited = h₁ at hch₁ hv₁ hvis₁ hown₁
  have yes {x : UInt8} (e : l.tag o = x) : (l.tag o == x) = true := by simp [e]
  have no {x : UInt8} (e : l.tag o ≠ x) : (l.tag o == x) = false := by simpa using e
  have nonull (hs : hasSlots (l.tag o) = true) : Member.null ∉ l.members o := by
    simpa [shapeOk, hs] using hshape
  by_cases hc : l.tag o ≤ LeanMaxCtorTag
  · simp only [hc, ↓reduceIte]
    have hs : hasSlots (l.tag o) = true := by simp [hasSlots, hc]
    exact slotted_safe g l hl o (fun x => decide (x ≤ LeanMaxCtorTag))
      (fun t => decide (t ≤ LeanMaxCtorTag) || t == LeanThunk || t == LeanRef) (by simp [hc])
      (by simp [hc]) hs (nonull hs) hsz h₁ hch₁ hvis₁ hv₁ hown₁
  simp only [hc, ↓reduceIte, coreOther]
  have hslots (h1 : l.tag o ≠ LeanClosure) (h2 : l.tag o ≠ LeanArray) :
      hasSlots (l.tag o) = false := by
    simp [hasSlots, hc, h1, h2]
  by_cases t1 : l.tag o = LeanClosure
  · simp only [yes t1, ↓reduceIte]
    have hs : hasSlots (l.tag o) = true := by simp [hasSlots, t1]
    exact slotted_safe g l hl o (· == LeanClosure) (· == LeanClosure) (yes t1) (yes t1) hs
      (nonull hs) hsz h₁ hch₁ hvis₁ hv₁ hown₁
  simp only [no t1, Bool.false_eq_true, ↓reduceIte]
  by_cases t2 : l.tag o = LeanArray
  · simp only [yes t2, ↓reduceIte]
    have hs : hasSlots (l.tag o) = true := by simp [hasSlots, t2]
    exact slotted_safe g l hl o (· == LeanArray) (· == LeanArray) (yes t2) (yes t2) hs
      (nonull hs) hsz h₁ hch₁ hvis₁ hv₁ hown₁
  simp only [no t2, Bool.false_eq_true, ↓reduceIte]
  have hshape' := hshape
  simp only [shapeOk, hslots t1 t2, Bool.false_eq_true, ↓reduceIte] at hshape'
  have hm := fun t (e : l.tag o = t) (ok : UInt8 → Bool) (hok : ok (l.tag o) = true) =>
    members_safe g l hl o t ok hok e h₁ (todo := todo) hch₁ hvis₁ hv₁ hown₁
  by_cases t6 : l.tag o = LeanThunk
  · simp only [yes t6, ↓reduceIte, beq_iff_eq] at hshape'
    obtain ⟨m₀, hms⟩ : ∃ m₀ m₁, l.members o = [m₀, m₁] := by
      match hm : l.members o, hshape' with
      | [m₀, m₁], _ => exact ⟨m₀, m₁, rfl⟩
    obtain ⟨m₁, hms⟩ := hms
    have t3 : l.tag o ≠ LeanScalarArray := by rw [t6]; decide
    have t4 : l.tag o ≠ LeanString := by rw [t6]; decide
    have t5 : l.tag o ≠ LeanMPZ := by rw [t6]; decide
    simp only [no t3, no t4, no t5, yes t6, Bool.false_eq_true, ↓reduceIte]
    exact (hm LeanThunk t6 (fun t => decide (t ≤ LeanMaxCtorTag) || t == LeanThunk || t == LeanRef)
      (by simp [t6])).1 m₀ m₁ hms
  simp only [no t6, Bool.false_eq_true, ↓reduceIte] at hshape' ⊢
  by_cases t7 : l.tag o = LeanRef
  · simp only [yes t7, ↓reduceIte, beq_iff_eq] at hshape'
    obtain ⟨m₀, hms⟩ := List.length_eq_one_iff.mp hshape'
    have t3 : l.tag o ≠ LeanScalarArray := by rw [t7]; decide
    have t4 : l.tag o ≠ LeanString := by rw [t7]; decide
    have t5 : l.tag o ≠ LeanMPZ := by rw [t7]; decide
    simp only [no t3, no t4, no t5, yes t7, Bool.false_eq_true, ↓reduceIte]
    exact (hm LeanRef t7 (fun t => decide (t ≤ LeanMaxCtorTag) || t == LeanThunk || t == LeanRef)
      (by simp [t7])).2 m₀ hms
  simp only [no t7, Bool.false_eq_true, ↓reduceIte] at hshape' ⊢
  by_cases t11 : l.tag o = LeanStructArray ∨ l.tag o = LeanReserved
  · exfalso
    rcases t11 with t11 | t11 <;> simp [yes t11] at hshape'
  have t11a : l.tag o ≠ LeanStructArray := fun e => t11 (.inl e)
  have t11b : l.tag o ≠ LeanReserved := fun e => t11 (.inr e)
  simp only [no t11a, no t11b, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    List.isEmpty_iff] at hshape'
  have leaf : ∀ ok : UInt8 → Bool, ok (l.tag o) = true →
      ((do reclaim l ok (.obj o); return todo : M objects roots fields _).run h₁).2.fault =
        h₁.fault := by
    intro ok hok
    simp only [run_bind]
    have hp : ∀ x, ((pure todo : M objects roots fields _).run x).2 = x := fun _ => rfl
    rw [hp]
    exact reclaim_safe l ok h₁ o hvis₁ hok (by simp [hshape'])
  by_cases t3 : l.tag o = LeanScalarArray
  · simp only [yes t3, ↓reduceIte]; exact leaf _ (yes t3)
  simp only [no t3, Bool.false_eq_true, ↓reduceIte]
  by_cases t4 : l.tag o = LeanString
  · simp only [yes t4, ↓reduceIte]; exact leaf _ (yes t4)
  simp only [no t4, Bool.false_eq_true, ↓reduceIte]
  by_cases t5 : l.tag o = LeanMPZ
  · simp only [yes t5, ↓reduceIte]; exact leaf _ (yes t5)
  simp only [no t5, Bool.false_eq_true, ↓reduceIte]
  by_cases t8 : l.tag o = LeanTask
  · simp only [yes t8, ↓reduceIte]; exact leaf _ (yes t8)
  simp only [no t8, Bool.false_eq_true, ↓reduceIte]
  by_cases t9 : l.tag o = LeanPromise
  · simp only [yes t9, ↓reduceIte]; exact leaf _ (yes t9)
  simp only [no t9, Bool.false_eq_true, ↓reduceIte]
  by_cases t10 : l.tag o = LeanExternal
  · simp only [yes t10, ↓reduceIte]; exact leaf _ (yes t10)
  exact absurd (tag_cases _ hc t1 t2 t3 t4 t5 t6 t7 t8 t9 t10) t11

/-- Every field of a queued object still holds its reference. -/
def Pending (g : Graph α objects roots fields) (s : State objects roots fields) : Prop :=
  ∀ q ∈ s.todo, ∀ f, g.source f = q → Token.field f ∈ s.own

/-- Dropping a field of a dead object leaves the fields of every other queued object owned. -/
theorem drop_pending {s : State objects roots fields} {o : Fin objects} {f₀ : Fin fields}
    (hsrc : g.source f₀ = o) (hdead : s.rc o = none) (hoL : o ∉ s.todo) (hv : Valid g s)
    (hp : Pending g s) : Pending g (drop g s (.field f₀)) := by
  intro q hq f hf
  have hqo : q ≠ o := by
    intro e; subst e
    rw [drop_todo_mem_none hdead] at hq
    exact hoL hq
  have hne : (Token.field f : Token roots fields) ≠ Token.field f₀ := fun e => by
    cases e; exact hqo (hf.symm.trans hsrc)
  rw [drop_own]
  rw [drop_todo, List.mem_append] at hq
  rcases hq with hq | hq
  · have hlive := (mem_dropPush.mp hq).1
    exact (List.mem_erase_of_ne hne).mpr (hv.2.1 f (by rw [hf]; exact hlive))
  · exact (List.mem_erase_of_ne hne).mpr (hp q hq f hf)

theorem scan_pending {o : Fin objects} :
    ∀ (fs : List (Fin fields)) {s : State objects roots fields}, (∀ f ∈ fs, g.source f = o) →
      s.rc o = none → o ∉ s.todo → Valid g s → Pending g s → Pending g (scan g s fs)
  | [], _, _, _, _, _, hp => hp
  | f :: fs, s, hsrc, hdead, hoL, hv, hp => by
    have hsrc₀ := hsrc f (by simp)
    exact scan_pending fs (fun f' hf' => hsrc f' (by simp [hf']))
      (drop_rc_none _ _ _ hdead) (by rw [drop_todo_mem_none hdead]; exact hoL)
      (drop_valid hv (by simp [Droppable, hsrc₀, hdead]))
      (drop_pending g hsrc₀ hdead hoL hv hp)

/-- Deleting the head of the worklist keeps the fields of the other queued objects owned. -/
theorem visit_pending {s : State objects roots fields} {o : Fin objects}
    {rest : List (Fin objects)} (htodo : s.todo = o :: rest) (hv : Valid g s) (hq : QueueSafe s)
    (hp : Pending g s) : Pending g (visit g { s with todo := rest } o) := by
  have hdead : s.rc o = none := hq.2 o (by simp [htodo])
  have hoL : o ∉ rest := by
    have := hq.1; rw [htodo] at this; exact fun h => (List.nodup_cons.mp this).1 (by simp [h])
  have hp' : Pending g { s with todo := rest } := fun q hq' => hp q (by simp [htodo, hq'])
  have := scan_pending g (o := o) (g.children o) (s := { s with todo := rest })
    (fun f hf => by simpa [Graph.children] using hf) hdead hoL hv hp'
  exact this

/--
`cascadeLoop` keeps the protocol on a valid heap whose queued objects still own
their fields.
-/
theorem resume_safe (hl : l.Valid g) (s : State objects roots fields) :
    ∀ (h : Heap objects roots fields) (todo : Val objects), Chain h.cell todo s.todo →
      h.state s.todo = s → Valid g s → QueueSafe s → Pending g s →
      ((resume (adapter g l) todo).run h).2.fault = h.fault := by
  fun_induction drain g s with
  | case1 s hs =>
    intro h todo hch heq _ _ _
    rw [hs] at hch
    cases hch
    rfl
  | case2 s o rest hs ih =>
    intro h todo hch heq hv hq hp
    rw [hs] at hch heq
    cases hch with
    | @cons _ next _ hqd hn =>
      have hoL : o ∉ rest := (List.nodup_cons.mp (Chain.cons hqd hn).nodup).1
      have hst : h.state rest = { s with todo := rest } := by rw [← heq]; rfl
      have ho : h.own = s.own := congrArg State.own heq
      have hown : ∀ f, Member.field f ∈ l.members o → Token.field f ∈ h.own := fun f hf =>
        ho ▸ hp o (by simp [hs]) f ((members_fields g l hl o).2 f hf)
      have hfault := core_safe g l hl h hn o hoL (.inr ⟨next, hqd⟩) (by rw [hst]; exact hv) hown
      have hcore := core_refines g l hl h hn o hoL (by simp [hqd])
      rw [hst] at hcore
      have hnull : (Val.obj o == Val.null) = false := rfl
      have hget : ((adapter g l).getNext (.obj o)).run h = (next, h) := by
        simp [StateT.run, getNext, hqd]
      have hrun : (resume (adapter g l) (.obj o)).run h =
          (resume (adapter g l) ((core (adapter g l) (.obj o) next).run h).1).run
            ((core (adapter g l) (.obj o) next).run h).2 := by
        conv => lhs; rw [resume]
        simp only [hnull, Bool.false_eq_true, ↓reduceIte]
        rw [run_bind, hget, cascadeLoop_eq, run_bind]
      obtain ⟨hv', hq'⟩ := pop_visit_safe hs hv hq
      rw [hrun, ← hfault]
      exact ih _ _ hcore.2 hcore.1 hv' hq' (visit_pending g hs hv hq hp)

/-- The cascade from an object this thread is responsible for keeps the protocol. -/
theorem cascade_safe (hl : l.Valid g) (h : Heap objects roots fields) (p : Fin objects)
    (hp : h.cell p = .last) (s : State objects roots fields) (hs : s.todo = [p])
    (heq : h.state [] = { s with todo := [] }) (hv : Valid g s) (hq : QueueSafe s)
    (hpend : Pending g s) :
    ((cascade (adapter g l) (.obj p)).run h).2.fault = h.fault := by
  have hown : ∀ f, Member.field f ∈ l.members p → Token.field f ∈ h.own := fun f hf => by
    have := hpend p (by simp [hs]) f ((members_fields g l hl p).2 f hf)
    have ho : h.own = s.own := congrArg State.own heq
    rw [ho]; exact this
  have hv₁ : Valid g (h.state []) := by rw [heq]; exact hv
  have hfault := core_safe g l hl h (L := []) .nil p (by simp) (.inl hp) hv₁ hown
  have hcore := core_refines g l hl h (L := []) .nil p (by simp) (by simp [hp])
  rw [heq] at hcore
  obtain ⟨hv', hq'⟩ := pop_visit_safe hs hv hq
  rw [cascade, cascadeLoop_eq, run_bind, ← hfault]
  exact resume_safe g l hl _ _ _ hcore.2 hcore.1 hv' hq' (visit_pending g hs hv hq hpend)

end Protocol

/--
On a heap between releases, releasing a root records no fault: every count, link, slot and
terminal effect the cascade touches is one that the heap's protocol allows.
-/
theorem collect_safe {g : Graph α objects roots fields} (l : Layout objects fields)
    (hl : l.Valid g) {s : State objects roots fields} (hs : Quiescent g s) (d : Fin roots) :
    (decRoot g l s d).fault = false := by
  unfold decRoot
  by_cases ht : Token.root d ∈ s.own
  · simp only [ht, ↓reduceIte]
    have h₀ : (Heap.ofState { s with own := s.own.erase (.root d) }).state [] =
        { s with own := s.own.erase (.root d) } := by
      simpa [hs.todo] using ofState_state { s with own := s.own.erase (.root d) }
    have hdrop := drop_eq_countDrop g s (.root d)
    simp only [ht, ↓reduceIte] at hdrop
    cases hrc : s.rc (g.root d) with
    | none => rfl
    | some rc =>
      simp only
      cases hdn : decRef rc with
      | some rc' => rfl
      | none =>
        simp only
        -- The cascade starts from the root's object, which is the only one queued after `drop`.
        have hs₁ : (drop g s (.root d)).todo = [g.root d] := by
          rw [hdrop]; simp [countDrop, hrc, hdn, hs.todo]
        have hpend : Pending g (drop g s (.root d)) := by
          intro q hq f hf
          rw [hs₁, List.mem_singleton] at hq
          subst hq
          rw [drop_own]
          exact (List.mem_erase_of_ne (by simp)).mpr
            (hs.valid.2.1 f (by rw [hf, hrc]; rfl))
        rw [cascade_safe g l hl _ (g.root d) (by simp) (drop g s (.root d)) hs₁ ?_
          (drop_valid hs.valid trivial) (drop_queueSafe hs.queueSafe) hpend]
        · rfl
        · rw [Heap.state_setCell, h₀, hdrop]
          simp [countDrop, hrc, hdn, hs.todo]
  · simp only [ht, ↓reduceIte]
    rfl

end RcGraph
