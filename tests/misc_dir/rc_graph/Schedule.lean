import Graph

/-!
Every deletion schedule reaches the same state.

`drain` fixes one schedule: last in, first out, releasing each object's fields in order before
reclaiming it. The native finalizer order is a byproduct of that schedule, not a contract. `Step`
permits any interleaving of releasing an owned field of an object that has lost its last reference
and reclaiming a queued object whose fields have all been released. `schedule_independent` proves
that every schedule run until no step applies ends with the same ownership and counters, and with
the same queued and reclaimed objects up to order. `drain` is one such schedule, and `Released`
states what releasing a root does, whatever the schedule.
-/

namespace RcGraph

variable {α : Type} {objects roots fields : Nat}

/-! ## `drop` as a function of ownership and counters -/

/-- The counters after `drop`. -/
def dropRc (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : Fin objects → Option Int32 :=
  if t ∈ s.own then set s.rc (g.dst t) ((s.rc (g.dst t)).bind decRef) else s.rc

/-- The objects that `drop` queues. -/
def dropPush (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : List (Fin objects) :=
  if t ∈ s.own ∧ (s.rc (g.dst t)).isSome ∧ (s.rc (g.dst t)).bind decRef = none then
    [g.dst t]
  else []

theorem drop_of_not_mem (g : Graph α objects roots fields) {s : State objects roots fields}
    {t : Token roots fields} (h : t ∉ s.own) : drop g s t = s := by
  simp [drop, h]

theorem drop_eq (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) :
    drop g s t =
      { own := s.own.erase t, rc := dropRc g s t, todo := dropPush g s t ++ s.todo,
        freed := s.freed } := by
  obtain ⟨own, rc, todo, freed⟩ := s
  by_cases ht : t ∈ own
  · cases hc : rc (g.dst t) with
    | none =>
      have hset : set rc (g.dst t) none = rc := by
        funext p
        by_cases hp : p = g.dst t <;> simp [set, hp, hc]
      simp [drop, dropRc, dropPush, ht, hc, hset]
    | some r =>
      cases hd : decRef r <;> simp [drop, dropRc, dropPush, ht, hc, hd]
  · simp [drop, dropRc, dropPush, ht, List.erase_of_not_mem ht]

theorem drop_rc (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : (drop g s t).rc = dropRc g s t := by
  rw [drop_eq]

theorem drop_todo (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : (drop g s t).todo = dropPush g s t ++ s.todo := by
  rw [drop_eq]

theorem dropPush_length (g : Graph α objects roots fields) (s : State objects roots fields)
    (t : Token roots fields) : (dropPush g s t).length ≤ 1 := by
  unfold dropPush
  split <;> simp

theorem not_mem_dropPush {g : Graph α objects roots fields} {s : State objects roots fields}
    {o : Fin objects} (h : s.rc o = none) (t : Token roots fields) : o ∉ dropPush g s t := by
  unfold dropPush
  split
  · rename_i hc
    simp only [List.mem_singleton]
    intro heq
    subst heq
    simp [h] at hc
  · simp

/-- A later drop to another target queues what it would have queued first. -/
theorem dropPush_drop_of_ne (g : Graph α objects roots fields) (s : State objects roots fields)
    {t₁ t₂ : Token roots fields} (hne : t₁ ≠ t₂) (hd : g.dst t₁ ≠ g.dst t₂) :
    dropPush g (drop g s t₁) t₂ = dropPush g s t₂ := by
  have m : t₂ ∈ s.own.erase t₁ ↔ t₂ ∈ s.own := List.mem_erase_of_ne (Ne.symm hne)
  have hrc : (drop g s t₁).rc (g.dst t₂) = s.rc (g.dst t₂) := drop_rc_other _ _ _ (Ne.symm hd)
  simp only [dropPush, drop_own, m, hrc]

/-- Two drops to one target queue it at most once, whichever comes first. -/
theorem dropPush_pair_of_eq (g : Graph α objects roots fields) (s : State objects roots fields)
    {t₁ t₂ : Token roots fields} (hne : t₁ ≠ t₂) (hd : g.dst t₁ = g.dst t₂) :
    dropPush g (drop g s t₁) t₂ ++ dropPush g s t₁ =
      dropPush g (drop g s t₂) t₁ ++ dropPush g s t₂ := by
  have m₁ : t₁ ∈ s.own.erase t₂ ↔ t₁ ∈ s.own := List.mem_erase_of_ne hne
  have m₂ : t₂ ∈ s.own.erase t₁ ↔ t₂ ∈ s.own := List.mem_erase_of_ne (Ne.symm hne)
  by_cases h₁ : t₁ ∈ s.own <;> by_cases h₂ : t₂ ∈ s.own
  · have r₁ : (drop g s t₁).rc (g.dst t₂) = (s.rc (g.dst t₂)).bind decRef := by
      rw [← hd]; exact drop_rc_target h₁
    have r₂ : (drop g s t₂).rc (g.dst t₂) = (s.rc (g.dst t₂)).bind decRef :=
      drop_rc_target h₂
    simp only [dropPush, drop_own, m₁, m₂, h₁, h₂, hd, r₁, r₂, true_and]
  · simp [dropPush, drop_own, m₂, h₂, drop_of_not_mem g h₂]
  · simp [dropPush, drop_own, m₁, h₁, drop_of_not_mem g h₁]
  · simp [dropPush, drop_own, m₁, m₂, h₁, h₂]

/-! ## Schedules -/

/-- Remove a queued object and record its reclamation. -/
def reclaimAt (s : State objects roots fields) (o : Fin objects) : State objects roots fields :=
  { s with todo := s.todo.erase o, freed := o :: s.freed }

@[simp] theorem reclaimAt_own (s : State objects roots fields) (o : Fin objects) :
    (reclaimAt s o).own = s.own := rfl

@[simp] theorem reclaimAt_rc (s : State objects roots fields) (o : Fin objects) :
    (reclaimAt s o).rc = s.rc := rfl

@[simp] theorem reclaimAt_todo (s : State objects roots fields) (o : Fin objects) :
    (reclaimAt s o).todo = s.todo.erase o := rfl

@[simp] theorem reclaimAt_freed (s : State objects roots fields) (o : Fin objects) :
    (reclaimAt s o).freed = o :: s.freed := rfl

/-- One deletion step. Steps may be taken in any order. -/
inductive Step (g : Graph α objects roots fields) :
    State objects roots fields → State objects roots fields → Prop
  /-- Release an owned field of an object that has lost its last reference. -/
  | release {s : State objects roots fields} {f : Fin fields} :
      .field f ∈ s.own → s.rc (g.source f) = none → Step g s (drop g s (.field f))
  /-- Reclaim a queued object after all of its fields have been released. -/
  | reclaim {s : State objects roots fields} {o : Fin objects} :
      o ∈ s.todo → (∀ f, g.source f = o → .field f ∉ s.own) → Step g s (reclaimAt s o)

/-- A finite schedule. -/
inductive Steps (g : Graph α objects roots fields) :
    State objects roots fields → State objects roots fields → Prop
  | refl (s : State objects roots fields) : Steps g s s
  | step {s s' t : State objects roots fields} : Step g s s' → Steps g s' t → Steps g s t

theorem Steps.trans {g : Graph α objects roots fields} {s t u : State objects roots fields}
    (h₁ : Steps g s t) (h₂ : Steps g t u) : Steps g s u := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem Steps.preserve {g : Graph α objects roots fields}
    {P : State objects roots fields → Prop} (hP : ∀ {s s'}, P s → Step g s s' → P s')
    {s t : State objects roots fields} (h : Steps g s t) (hs : P s) : P t := by
  induction h with
  | refl => exact hs
  | step h _ ih => exact ih (hP hs h)

/-- No step applies. -/
def Stuck (g : Graph α objects roots fields) (s : State objects roots fields) : Prop :=
  ∀ s', ¬ Step g s s'

/-- Equal ownership and counters; the worklist and reclamation trace may differ in order. -/
structure Equiv (s t : State objects roots fields) : Prop where
  own : s.own = t.own
  rc : s.rc = t.rc
  todo : s.todo.Perm t.todo
  freed : s.freed.Perm t.freed

theorem Equiv.refl (s : State objects roots fields) : Equiv s s :=
  ⟨rfl, rfl, .refl _, .refl _⟩

theorem Equiv.symm {s t : State objects roots fields} (h : Equiv s t) : Equiv t s :=
  ⟨h.own.symm, h.rc.symm, h.todo.symm, h.freed.symm⟩

theorem Equiv.trans {s t u : State objects roots fields} (h₁ : Equiv s t) (h₂ : Equiv t u) :
    Equiv s u :=
  ⟨h₁.own.trans h₂.own, h₁.rc.trans h₂.rc, h₁.todo.trans h₂.todo, h₁.freed.trans h₂.freed⟩

/-- Releasing consumes a token and queues at most one object; reclaiming consumes a queued one. -/
def stepWeight (s : State objects roots fields) : Nat := 2 * s.own.length + s.todo.length

theorem Step.weight_lt {g : Graph α objects roots fields} {s s' : State objects roots fields}
    (h : Step g s s') : stepWeight s' < stepWeight s := by
  cases h with
  | @release f hf _ =>
    have hl := List.length_erase_of_mem hf
    have hp := List.length_pos_of_mem hf
    have hd := dropPush_length g s (.field f)
    simp only [stepWeight, drop_own, drop_todo, List.length_append]
    omega
  | @reclaim o ho _ =>
    have hl := List.length_erase_of_mem ho
    have hp := List.length_pos_of_mem ho
    simp only [stepWeight, reclaimAt_own, reclaimAt_todo]
    omega

theorem Equiv.weight_eq {s t : State objects roots fields} (h : Equiv s t) :
    stepWeight s = stepWeight t := by
  simp only [stepWeight, h.own, h.todo.length_eq]

/-- Equivalent states take matching steps. -/
theorem Step.equiv {g : Graph α objects roots fields} {s t s' : State objects roots fields}
    (hst : Equiv s t) (h : Step g s s') : ∃ t', Step g t t' ∧ Equiv s' t' := by
  cases h with
  | @release f hf hs =>
    refine ⟨drop g t (.field f), .release (hst.own ▸ hf) (hst.rc ▸ hs), ?_⟩
    rw [drop_eq, drop_eq]
    refine ⟨by simp [hst.own], ?_, ?_, hst.freed⟩
    · simp only [dropRc, hst.own, hst.rc]
    · simp only [dropPush, hst.own, hst.rc]
      exact List.Perm.append_left _ hst.todo
  | @reclaim o ho hfs =>
    refine ⟨reclaimAt t o,
      .reclaim (hst.todo.mem_iff.mp ho) (fun f hf => hst.own ▸ hfs f hf), ?_⟩
    exact ⟨hst.own, hst.rc, hst.todo.erase o, hst.freed.cons o⟩

theorem Stuck.equiv {g : Graph α objects roots fields} {s t : State objects roots fields}
    (hs : Stuck g s) (hst : Equiv s t) : Stuck g t := by
  intro t' ht
  obtain ⟨s', hs', -⟩ := ht.equiv hst.symm
  exact hs s' hs'

theorem QueueSafe.equiv {s t : State objects roots fields} (hq : QueueSafe s)
    (hst : Equiv s t) : QueueSafe t := by
  have hp : (s.todo ++ s.freed).Perm (t.todo ++ t.freed) := hst.todo.append hst.freed
  refine ⟨hp.nodup_iff.mp hq.1, fun o ho => ?_⟩
  rw [← hst.rc]
  exact hq.2 o (hp.mem_iff.mpr ho)

theorem Step.queueSafe {g : Graph α objects roots fields} {s s' : State objects roots fields}
    (hq : QueueSafe s) (h : Step g s s') : QueueSafe s' := by
  cases h with
  | release _ _ => exact drop_queueSafe hq
  | @reclaim o ho _ =>
    have hp : (s.todo.erase o ++ o :: s.freed).Perm (s.todo ++ s.freed) :=
      List.perm_middle.trans ((List.perm_cons_erase ho).append_right s.freed).symm
    exact ⟨hp.nodup_iff.mpr hq.1, fun p hp' => hq.2 p (hp.mem_iff.mp hp')⟩

/-! ## Local commutation -/

/-- Two drops of distinct tokens commute, up to the order of what they queue. -/
theorem drop_drop_equiv (g : Graph α objects roots fields) (s : State objects roots fields)
    {t₁ t₂ : Token roots fields} (hne : t₁ ≠ t₂) :
    Equiv (drop g (drop g s t₁) t₂) (drop g (drop g s t₂) t₁) := by
  have m₁ : t₁ ∈ s.own.erase t₂ ↔ t₁ ∈ s.own := List.mem_erase_of_ne hne
  have m₂ : t₂ ∈ s.own.erase t₁ ↔ t₂ ∈ s.own := List.mem_erase_of_ne (Ne.symm hne)
  refine ⟨by simp [List.erase_comm], ?_, ?_, by simp⟩
  · rw [drop_rc, drop_rc]
    funext p
    simp only [dropRc, drop_own, drop_rc, m₁, m₂]
    by_cases h₁ : t₁ ∈ s.own <;> by_cases h₂ : t₂ ∈ s.own <;>
      simp only [h₁, h₂, ↓reduceIte, set] <;> split <;> split <;> simp_all
  · rw [drop_todo, drop_todo, drop_todo, drop_todo, ← List.append_assoc, ← List.append_assoc]
    apply List.Perm.append_right
    by_cases hd : g.dst t₁ = g.dst t₂
    · rw [dropPush_pair_of_eq g s hne hd]
    · rw [dropPush_drop_of_ne g s hne hd, dropPush_drop_of_ne g s (Ne.symm hne) (Ne.symm hd)]
      exact List.perm_append_comm

/-- Releasing a field and reclaiming a queued object commute. -/
theorem release_reclaim {g : Graph α objects roots fields} {s : State objects roots fields}
    (hq : QueueSafe s) {f : Fin fields} {o : Fin objects}
    (hf : .field f ∈ s.own) (hs : s.rc (g.source f) = none)
    (ho : o ∈ s.todo) (hfs : ∀ f, g.source f = o → .field f ∉ s.own) :
    Step g (drop g s (.field f)) (reclaimAt (drop g s (.field f)) o) ∧
      Step g (reclaimAt s o) (drop g (reclaimAt s o) (.field f)) ∧
      Equiv (reclaimAt (drop g s (.field f)) o) (drop g (reclaimAt s o) (.field f)) := by
  have hn : o ∉ dropPush g s (.field f) := not_mem_dropPush (hq.2 o (by simp [ho])) _
  refine ⟨.reclaim ?_ ?_, .release hf hs, ?_⟩
  · simp [drop_todo, ho]
  · intro f' hf' hm
    exact hfs f' hf' (List.mem_of_mem_erase (by simpa using hm))
  · rw [drop_eq, drop_eq]
    refine ⟨rfl, rfl, .of_eq ?_, .refl _⟩
    simp only [reclaimAt_todo]
    exact List.erase_append_right _ hn

/-- Two enabled steps are equal or can be completed to equivalent states, one step each. -/
theorem Step.diamond {g : Graph α objects roots fields} {s s₁ s₂ : State objects roots fields}
    (hq : QueueSafe s) (h₁ : Step g s s₁) (h₂ : Step g s s₂) :
    Equiv s₁ s₂ ∨ ∃ u₁ u₂, Step g s₁ u₁ ∧ Step g s₂ u₂ ∧ Equiv u₁ u₂ := by
  cases h₁ with
  | @release f₁ hf₁ hs₁ =>
    cases h₂ with
    | @release f₂ hf₂ hs₂ =>
      by_cases hf : f₁ = f₂
      · subst hf
        exact .inl (.refl _)
      · have hne : (Token.field f₁ : Token roots fields) ≠ .field f₂ := by simpa using hf
        refine .inr ⟨_, _, .release ?_ (drop_rc_none _ _ _ hs₂),
          .release ?_ (drop_rc_none _ _ _ hs₁), drop_drop_equiv g s hne⟩
        · simpa [List.mem_erase_of_ne (Ne.symm hne)] using hf₂
        · simpa [List.mem_erase_of_ne hne] using hf₁
    | @reclaim o ho hfs =>
      obtain ⟨a, b, e⟩ := release_reclaim hq hf₁ hs₁ ho hfs
      exact .inr ⟨_, _, a, b, e⟩
  | @reclaim o₁ ho₁ hfs₁ =>
    cases h₂ with
    | @release f hf hs =>
      obtain ⟨a, b, e⟩ := release_reclaim hq hf hs ho₁ hfs₁
      exact .inr ⟨_, _, b, a, e.symm⟩
    | @reclaim o₂ ho₂ hfs₂ =>
      by_cases ho : o₁ = o₂
      · subst ho
        exact .inl (.refl _)
      · refine .inr ⟨_, _, .reclaim ?_ hfs₂, .reclaim ?_ hfs₁, ?_⟩
        · exact (List.mem_erase_of_ne (Ne.symm ho)).mpr ho₂
        · exact (List.mem_erase_of_ne ho).mpr ho₁
        · exact ⟨rfl, rfl, .of_eq (List.erase_comm _ _), .swap _ _ _⟩

/-! ## Determinacy -/

private theorem exists_stuck_aux (g : Graph α objects roots fields) :
    ∀ (n : Nat) (s : State objects roots fields), stepWeight s < n →
      ∃ a, Steps g s a ∧ Stuck g a
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, h => by
    by_cases hs : ∃ s', Step g s s'
    · obtain ⟨s', hs'⟩ := hs
      obtain ⟨a, ha, hsa⟩ := exists_stuck_aux g n s' (by have := hs'.weight_lt; omega)
      exact ⟨a, .step hs' ha, hsa⟩
    · exact ⟨s, .refl s, fun s' h' => hs ⟨s', h'⟩⟩

/-- Every state has a schedule that runs until no step applies. -/
theorem exists_stuck (g : Graph α objects roots fields) (s : State objects roots fields) :
    ∃ a, Steps g s a ∧ Stuck g a :=
  exists_stuck_aux g _ s (Nat.lt_succ_self _)

private theorem stuck_unique_aux {g : Graph α objects roots fields} (n : Nat) :
    ∀ {s t a b : State objects roots fields}, stepWeight s < n → QueueSafe s → Equiv s t →
      Steps g s a → Stuck g a → Steps g t b → Stuck g b → Equiv a b := by
  induction n with
  | zero => intro _ _ _ _ hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro s t a b hn hq hst ha hsa hb hsb
    cases ha with
    | refl =>
      cases hb with
      | refl => exact hst
      | step h _ => exact absurd h (hsa.equiv hst _)
    | step h₁ ha' =>
      obtain ⟨t₁, ht₁, he₁⟩ := h₁.equiv hst
      cases hb with
      | refl => exact absurd ht₁ (hsb _)
      | step h₂ hb' =>
        have hqt := hq.equiv hst
        have w₁ := h₁.weight_lt
        have w₂ := h₂.weight_lt
        have wt := hst.weight_eq
        have we₁ := he₁.weight_eq
        rcases Step.diamond hqt ht₁ h₂ with he | ⟨u₁, u₂, hu₁, hu₂, heu⟩
        · exact ih (by omega) (h₁.queueSafe hq) (he₁.trans he) ha' hsa hb' hsb
        · obtain ⟨c, hc, hsc⟩ := exists_stuck g u₁
          obtain ⟨c₂, hc₂, hsc₂⟩ := exists_stuck g u₂
          have wu₁ := hu₁.weight_lt
          have e₁ := ih (by omega) (h₁.queueSafe hq) he₁ ha' hsa (.step hu₁ hc) hsc
          have e₂ := ih (by omega) (hu₁.queueSafe (ht₁.queueSafe hqt)) heu hc hsc hc₂ hsc₂
          have e₃ := ih (by omega) (h₂.queueSafe hqt) (.refl _) hb' hsb (.step hu₂ hc₂) hsc₂
          exact e₁.trans (e₂.trans e₃.symm)

/--
Every schedule run until no step applies reaches the same ownership and counters, and the same
queued and reclaimed objects up to order.
-/
theorem schedule_independent {g : Graph α objects roots fields}
    {s a b : State objects roots fields} (hq : QueueSafe s)
    (ha : Steps g s a) (hsa : Stuck g a) (hb : Steps g s b) (hsb : Stuck g b) : Equiv a b :=
  stuck_unique_aux _ (Nat.lt_succ_self _) hq (.refl s) ha hsa hb hsb

/-! ## `drain` is one schedule -/

/-- Append to the worklist. -/
def appendTodo (s : State objects roots fields) (l : List (Fin objects)) :
    State objects roots fields :=
  { s with todo := s.todo ++ l }

theorem drop_appendTodo (g : Graph α objects roots fields) (s : State objects roots fields)
    (l : List (Fin objects)) (t : Token roots fields) :
    drop g (appendTodo s l) t = appendTodo (drop g s t) l := by
  rw [drop_eq, drop_eq]
  simp only [appendTodo, List.append_assoc]
  rfl

theorem scan_appendTodo (g : Graph α objects roots fields) (s : State objects roots fields)
    (l : List (Fin objects)) (fs : List (Fin fields)) :
    scan g (appendTodo s l) fs = appendTodo (scan g s fs) l := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    change scan g (drop g (appendTodo s l) (.field f)) fs =
      appendTodo (scan g (drop g s (.field f)) fs) l
    rw [drop_appendTodo, ih]

theorem scan_steps {g : Graph α objects roots fields} {o : Fin objects}
    (fs : List (Fin fields)) (hfs : ∀ f ∈ fs, g.source f = o) (s : State objects roots fields)
    (ho : s.rc o = none) : Steps g s (scan g s fs) := by
  induction fs generalizing s with
  | nil => exact .refl _
  | cons f fs ih =>
    change Steps g s (scan g (drop g s (.field f)) fs)
    have ih' := ih (fun f' h' => hfs f' (by simp [h']))
    by_cases hf : .field f ∈ s.own
    · have hs : s.rc (g.source f) = none := by rw [hfs f (by simp)]; exact ho
      exact .step (.release hf hs) (ih' _ (drop_rc_none _ _ _ ho))
    · rw [drop_of_not_mem g hf]
      exact ih' _ ho

/-- Visiting the head is a schedule: release its fields in order, then reclaim it. -/
theorem visit_steps {g : Graph α objects roots fields} {s : State objects roots fields}
    {o : Fin objects} {rest : List (Fin objects)} (h : s.todo = o :: rest)
    (hv : Valid g s) (hq : QueueSafe s) : Steps g s (visit g { s with todo := rest } o) := by
  have ho : s.rc o = none := hq.2 o (by simp [h])
  have hmem : o ∈ (scan g s (g.children o)).todo := by
    rw [scan_todo_mem_none ho]; simp [h]
  have hfree : ∀ f, g.source f = o → .field f ∉ (scan g s (g.children o)).own :=
    fun f hf => scan_field_absent g s hv.1 _ (by simp [Graph.children, hf])
  have steps := (scan_steps (g.children o) (fun f hf => by simpa [Graph.children] using hf)
    s ho).trans (.step (.reclaim hmem hfree) (.refl _))
  suffices e : reclaimAt (scan g s (g.children o)) o = visit g { s with todo := rest } o by
    rwa [e] at steps
  obtain ⟨own, rc, todo, freed⟩ := s
  simp only at h
  subst h
  have hx : o ∉ (scan g ⟨own, rc, [], freed⟩ (g.children o)).todo := by
    rw [scan_todo_mem_none (s := ⟨own, rc, [], freed⟩) ho]; simp
  have e₁ := scan_appendTodo g ⟨own, rc, [], freed⟩ (o :: rest) (g.children o)
  have e₂ := scan_appendTodo g ⟨own, rc, [], freed⟩ rest (g.children o)
  simp only [appendTodo, List.nil_append] at e₁ e₂
  simp only [visit, reclaimAt, e₁, e₂, List.erase_append_right _ hx, List.erase_cons_head]

theorem drain_steps {g : Graph α objects roots fields} {s : State objects roots fields}
    (hv : Valid g s) (hq : QueueSafe s) : Steps g s (drain g s) := by
  fun_induction drain g s with
  | case1 => exact .refl _
  | case2 s o todo h ih =>
    obtain ⟨hv', hq'⟩ := pop_visit_safe h hv hq
    exact (visit_steps h hv hq).trans (ih hv' hq')

/-- Every owned field of an object that has lost its last reference belongs to a queued object. -/
def Accounted (g : Graph α objects roots fields) (s : State objects roots fields) : Prop :=
  ∀ f, .field f ∈ s.own → s.rc (g.source f) = none → g.source f ∈ s.todo

/-- `drop` queues exactly the object whose last reference it consumes. -/
theorem mem_dropPush {g : Graph α objects roots fields} {s : State objects roots fields}
    {t : Token roots fields} {o : Fin objects} :
    o ∈ dropPush g s t ↔ (s.rc o).isSome ∧ (drop g s t).rc o = none := by
  rw [drop_rc]
  unfold dropPush dropRc
  by_cases ht : t ∈ s.own
  · by_cases ho : o = g.dst t
    · subst ho
      cases s.rc (g.dst t) <;> simp [ht, set]
    · simp [ht, ho, set, Option.isSome_iff_ne_none]
  · simp [ht, Option.isSome_iff_ne_none]

theorem drop_accounted {g : Graph α objects roots fields} {s : State objects roots fields}
    (ha : Accounted g s) (t : Token roots fields) : Accounted g (drop g s t) := by
  intro f hf hs
  rw [drop_todo]
  have hf' : .field f ∈ s.own := List.mem_of_mem_erase (by simpa using hf)
  cases hc : s.rc (g.source f) with
  | none => exact List.mem_append_right _ (ha f hf' hc)
  | some r => exact List.mem_append_left _ (mem_dropPush.mpr ⟨by simp [hc], hs⟩)

theorem Step.valid {g : Graph α objects roots fields} {s s' : State objects roots fields}
    (hv : Valid g s) (h : Step g s s') : Valid g s' := by
  cases h with
  | release _ hs => exact drop_valid hv hs
  | reclaim _ _ => exact hv

theorem Step.accounted {g : Graph α objects roots fields} {s s' : State objects roots fields}
    (ha : Accounted g s) (h : Step g s s') : Accounted g s' := by
  cases h with
  | release _ _ => exact drop_accounted ha _
  | @reclaim o _ hfs =>
    intro f hf hs
    exact (List.mem_erase_of_ne fun heq => hfs f heq hf).mpr (ha f hf hs)

/-- Validity, queue safety and accounting hold throughout every schedule. -/
theorem Steps.safe {g : Graph α objects roots fields} {s t : State objects roots fields}
    (h : Steps g s t) (hv : Valid g s) (hq : QueueSafe s) (ha : Accounted g s) :
    Valid g t ∧ QueueSafe t ∧ Accounted g t :=
  h.preserve (P := fun s => Valid g s ∧ QueueSafe s ∧ Accounted g s)
    (fun hs h => ⟨h.valid hs.1, h.queueSafe hs.2.1, h.accounted hs.2.2⟩) ⟨hv, hq, ha⟩

/-- A schedule can stop only when the worklist is empty. -/
theorem Stuck.todo_eq_nil {g : Graph α objects roots fields} {s : State objects roots fields}
    (hs : Stuck g s) (hq : QueueSafe s) : s.todo = [] := by
  cases ht : s.todo with
  | nil => rfl
  | cons o rest =>
    have ho : s.rc o = none := hq.2 o (by simp [ht])
    by_cases hf : ∃ f, g.source f = o ∧ .field f ∈ s.own
    · obtain ⟨f, hfo, hf⟩ := hf
      exact absurd (Step.release hf (hfo ▸ ho)) (hs _)
    · exact absurd (Step.reclaim (by simp [ht]) fun f hfo hm => hf ⟨f, hfo, hm⟩) (hs _)

theorem drain_stuck {g : Graph α objects roots fields} {s : State objects roots fields}
    (hv : Valid g s) (hq : QueueSafe s) (ha : Accounted g s) : Stuck g (drain g s) := by
  have ha' := ((drain_steps hv hq).safe hv hq ha).2.2
  intro s' h
  cases h with
  | release hf hs => simpa using ha' _ hf hs
  | reclaim ho _ => simp at ho

/-- Every schedule run until no step applies agrees with `drain`. -/
theorem schedule_drain {g : Graph α objects roots fields} {s a : State objects roots fields}
    (hv : Valid g s) (hq : QueueSafe s) (ha : Accounted g s)
    (hr : Steps g s a) (hs : Stuck g a) : Equiv a (drain g s) :=
  schedule_independent hq hr hs (drain_steps hv hq) (drain_stuck hv hq ha)

/-! ## What a release does -/

/-- Between releases: nothing is queued, and every owned field belongs to a live object. -/
structure Quiescent (g : Graph α objects roots fields) (s : State objects roots fields) :
    Prop where
  valid : Valid g s
  queueSafe : QueueSafe s
  todo : s.todo = []
  fields : ∀ f, .field f ∈ s.own → (s.rc (g.source f)).isSome

/-- Facts that every schedule maintains after `s₀` releases a root and becomes `s₁`. -/
structure Inv (g : Graph α objects roots fields) (s₀ s₁ s : State objects roots fields) :
    Prop where
  valid : Valid g s
  queueSafe : QueueSafe s
  accounted : Accounted g s
  complete : Complete g s
  own : s.own ⊆ s₁.own
  freed : s₁.freed ⊆ s.freed
  roots : ∀ r, .root r ∈ s.own ↔ .root r ∈ s₁.own
  live : ∀ o, (s.rc o).isSome → (s₀.rc o).isSome
  fresh : ∀ o ∈ s.todo ++ s.freed, o ∈ s₀.freed ∨ (s₀.rc o).isSome
  caught : ∀ o, (s₀.rc o).isSome → s.rc o = none → o ∈ s.todo ++ s.freed

theorem Inv.start {g : Graph α objects roots fields} {s₀ : State objects roots fields}
    (hs : Quiescent g s₀) (d : Fin roots) :
    Inv g s₀ (drop g s₀ (.root d)) (drop g s₀ (.root d)) := by
  have hc : Complete g s₀ := fun f hf ht => by
    have := hs.fields f ht
    simp [hs.queueSafe.2 _ (List.mem_append_right _ hf)] at this
  refine ⟨drop_valid hs.valid trivial, drop_queueSafe hs.queueSafe, ?_, drop_complete hc _,
    List.Subset.refl _, List.Subset.refl _, fun _ => .rfl, fun o ho => drop_live_before ho,
    ?_, ?_⟩
  · intro f hf hn
    have hf' : .field f ∈ s₀.own := by simpa using hf
    rw [drop_todo]
    exact List.mem_append_left _ (mem_dropPush.mpr ⟨hs.fields f hf', hn⟩)
  · intro o ho
    rw [drop_todo, drop_freed, hs.todo, List.append_nil, List.mem_append] at ho
    rcases ho with ho | ho
    · exact .inr (mem_dropPush.mp ho).1
    · exact .inl ho
  · intro o h0 hn
    rw [drop_todo, drop_freed, hs.todo, List.append_nil]
    exact List.mem_append_left _ (mem_dropPush.mpr ⟨h0, hn⟩)

theorem Inv.step {g : Graph α objects roots fields} {s₀ s₁ s s' : State objects roots fields}
    (h : Inv g s₀ s₁ s) (hs : Step g s s') : Inv g s₀ s₁ s' := by
  cases hs with
  | @release f hf hsrc =>
    refine ⟨drop_valid h.valid hsrc, drop_queueSafe h.queueSafe, drop_accounted h.accounted _,
      drop_complete h.complete _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact h.own (List.mem_of_mem_erase (by simpa using ht))
    · simpa using h.freed
    · intro r
      rw [drop_root_mem]
      exact h.roots r
    · intro o ho
      exact h.live o (drop_live_before ho)
    · intro o ho
      rw [drop_todo, drop_freed, List.append_assoc, List.mem_append] at ho
      rcases ho with ho | ho
      · exact .inr (h.live o (mem_dropPush.mp ho).1)
      · exact h.fresh o ho
    · intro o h0 hn
      rw [drop_todo, drop_freed, List.append_assoc, List.mem_append]
      cases hc : s.rc o with
      | none => exact .inr (h.caught o h0 hc)
      | some r => exact .inl (mem_dropPush.mpr ⟨by simp [hc], hn⟩)
  | @reclaim o ho hfs =>
    have hp : (s.todo.erase o ++ o :: s.freed).Perm (s.todo ++ s.freed) :=
      List.perm_middle.trans ((List.perm_cons_erase ho).append_right s.freed).symm
    refine ⟨h.valid, (Step.reclaim ho hfs).queueSafe h.queueSafe,
      (Step.reclaim ho hfs).accounted h.accounted, ?_, h.own, ?_, h.roots, h.live, ?_, ?_⟩
    · intro f hf
      simp only [reclaimAt_freed, List.mem_cons] at hf
      rcases hf with hf | hf
      · exact hfs f hf
      · exact h.complete f hf
    · intro p hp'
      exact List.mem_cons_of_mem _ (h.freed hp')
    · intro p hp'
      exact h.fresh p (hp.mem_iff.mp hp')
    · intro p h0 hn
      exact hp.mem_iff.mpr (h.caught p h0 hn)

/-- What releasing root `d` of `s` does, whatever the schedule. -/
structure Released (g : Graph α objects roots fields) (s : State objects roots fields)
    (d : Fin roots) (a : State objects roots fields) : Prop where
  /-- Counters match the remaining references, and every live object keeps its fields. -/
  valid : Valid g a
  /-- Nothing remains queued. -/
  todo : a.todo = []
  /-- No object is reclaimed twice, and every reclaimed object has lost its last reference. -/
  queueSafe : QueueSafe a
  /-- Reclaimed: the earlier objects, and exactly those that lost their last reference. -/
  freed : ∀ o, o ∈ a.freed ↔ o ∈ s.freed ∨ ((s.rc o).isSome ∧ a.rc o = none)
  /-- Released: the root, and exactly the fields of reclaimed objects. -/
  own : ∀ t, t ∈ a.own ↔ t ∈ s.own ∧ t ≠ .root d ∧ ∀ f, t = .field f → g.source f ∉ a.freed
  /-- Objects reachable from another remaining root stay live with their payloads. -/
  observations : ∀ r, r ≠ d → .root r ∈ s.own → ∀ o, Reachable g r o →
    observe g a o = observe g s o

/-- Every schedule that releases root `d` and runs until no step applies does the same thing. -/
theorem release_schedule {g : Graph α objects roots fields} {s a : State objects roots fields}
    {d : Fin roots} (hs : Quiescent g s) (hr : Steps g (drop g s (.root d)) a)
    (hst : Stuck g a) : Released g s d a := by
  have h := hr.preserve (P := Inv g s (drop g s (.root d))) (fun h hs => h.step hs)
    (Inv.start hs d)
  have htodo := hst.todo_eq_nil h.queueSafe
  have hfreed : ∀ o, o ∈ a.freed ↔ o ∈ s.freed ∨ ((s.rc o).isSome ∧ a.rc o = none) := by
    intro o
    constructor
    · intro ho
      have hn := h.queueSafe.2 o (List.mem_append_right _ ho)
      rcases h.fresh o (List.mem_append_right _ ho) with h' | h'
      · exact .inl h'
      · exact .inr ⟨h', hn⟩
    · rintro (ho | ⟨h0, hn⟩)
      · exact h.freed (by simpa using ho)
      · simpa [htodo] using h.caught o h0 hn
  refine ⟨h.valid, htodo, h.queueSafe, hfreed, ?_, ?_⟩
  · intro t
    constructor
    · intro ht
      have ht₁ : t ∈ s.own.erase (.root d) := by simpa using h.own ht
      refine ⟨List.mem_of_mem_erase ht₁, ?_, ?_⟩
      · rintro rfl
        exact hs.valid.1.not_mem_erase ht₁
      · rintro f rfl hf
        exact h.complete f hf ht
    · rintro ⟨ht, hne, hf⟩
      cases t with
      | root r =>
        rw [h.roots r, drop_own]
        exact (List.mem_erase_of_ne hne).mpr ht
      | field f =>
        cases hc : a.rc (g.source f) with
        | some _ => exact h.valid.2.1 f (by simp [hc])
        | none => exact absurd ((hfreed _).mpr (.inr ⟨hs.fields f ht, hc⟩)) (hf f rfl)
  · intro r hne hr o hp
    have hra : .root r ∈ a.own := by
      rw [h.roots r, drop_own]
      exact (List.mem_erase_of_ne (by simpa using hne)).mpr hr
    have before := reachable_live hs.valid hr hp
    have after := reachable_live h.valid hra hp
    simp [observe, before, after]

/-- A release ends in a state between releases, so releases compose. -/
theorem Released.quiescent {g : Graph α objects roots fields}
    {s a : State objects roots fields} {d : Fin roots} (hs : Quiescent g s)
    (h : Released g s d a) : Quiescent g a := by
  refine ⟨h.valid, h.queueSafe, h.todo, fun f hf => ?_⟩
  obtain ⟨hf₀, -, hsrc⟩ := (h.own _).mp hf
  cases hc : a.rc (g.source f) with
  | some _ => rfl
  | none => exact absurd ((h.freed _).mpr (.inr ⟨hs.fields f hf₀, hc⟩)) (hsrc f rfl)

theorem Released.nodup {g : Graph α objects roots fields} {s a : State objects roots fields}
    {d : Fin roots} (h : Released g s d a) : a.freed.Nodup := by
  simpa [h.todo] using h.queueSafe.1

theorem Released.complete {g : Graph α objects roots fields}
    {s a : State objects roots fields} {d : Fin roots} (h : Released g s d a) : Complete g a :=
  fun f hf ht => ((h.own _).mp ht).2.2 f rfl hf

/-- `drain` releases root `d` as `Released` says, and every complete schedule agrees with it. -/
theorem drain_released {g : Graph α objects roots fields} {s : State objects roots fields}
    (hs : Quiescent g s) (d : Fin roots) :
    Released g s d (drain g (drop g s (.root d))) ∧
      ∀ a, Steps g (drop g s (.root d)) a → Stuck g a →
        Equiv a (drain g (drop g s (.root d))) := by
  have h := Inv.start hs d
  exact ⟨release_schedule hs (drain_steps h.valid h.queueSafe)
      (drain_stuck h.valid h.queueSafe h.accounted),
    fun a ha hsa => schedule_drain h.valid h.queueSafe h.accounted ha hsa⟩

end RcGraph
