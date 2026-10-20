import Schedule
import Collector

/-!
Refinement of the shared Lean collector into the finite ownership graph.
The entry point, direct child continuation, queue insertion, thunk dispatch, and field loop are shared with
the native specialization. The heap adapter interprets counters through the shared scalar decision
and records intrusive-link writes before viewing the new worklist.
-/

namespace RcGraph

/-- Interpret the atomic primitive at its linearization point in a serial cascade. -/
def fetchAdd : StateM Int32 Int32 := fun rc => (rc, rc + 1)

/-- The pure heap adapter uses the production counter control flow. -/
def releaseCount (rc : Int32) : Option Int32 :=
  let (last, rc') := (Lean.Runtime.GC.releaseLast StateT.get StateT.set fetchAdd).run rc
  if last then none else some rc'

theorem releaseCount_refines (rc : Int32) : releaseCount rc = decRef rc := by
  change (let (last, rc') :=
      (if rc > (1 : Int32) then fun _ => (false, rc - 1)
       else if rc == 1 then fun s => (true, s)
       else fun s =>
         (if s == 0 || s ≤ LEAN_RC_STICKY_DROP then fun s' => (false, s')
          else fun s' => (s' == -1, s' + 1)) s) rc
    if last then none else some rc') = decRef rc
  by_cases hgt : 1 < rc
  · simp [hgt, decRef]
  · by_cases heq : rc = 1
    · subst rc; rfl
    · by_cases hz : rc = 0
      · subst rc; rfl
      · by_cases hs : rc ≤ LEAN_RC_STICKY_DROP
        all_goals
          simp only [hgt, heq, hz, hs, decRef, decRefCold, Id.run, pure,
            beq_iff_eq, bne_iff_ne, Bool.or_eq_true, ↓reduceIte]
          try split <;> (try split) <;> simp_all <;> bv_decide

structure Heap (objects roots fields : Nat) where
  own : Ownership roots fields
  rc : Fin objects → Option Int32
  freed : List (Fin objects)
  next : Fin objects → List (Fin objects)

def Heap.state (h : Heap objects roots fields) (todo : List (Fin objects)) :
    State objects roots fields :=
  { own := h.own, rc := h.rc, freed := h.freed, todo }

def Heap.ofState (s : State objects roots fields) : Heap objects roots fields :=
  { own := s.own, rc := s.rc, freed := s.freed, next := fun _ => [] }

def project (r : List (Fin objects) × Heap objects roots fields) : State objects roots fields :=
  r.2.state r.1

/-- `none` represents a null or immediate field and owns no graph reference. -/
def dropRef (g : Graph α objects roots fields) (s : State objects roots fields)
    (r : Option (Token roots fields)) : State objects roots fields :=
  r.elim s (drop g s)

/-- Consume an ownership token at the counter's linearization point, without queuing anything. -/
def countStep (g : Graph α objects roots fields) (r : Option (Token roots fields)) :
    StateM (Heap objects roots fields) Bool := fun h =>
  match r with
  | none => (false, h)
  | some t =>
    if t ∈ h.own then
      let h := { h with own := h.own.erase t }
      match h.rc (g.dst t) with
      | none => (false, h)
      | some rc =>
        match releaseCount rc with
        | none => (true, { h with rc := set h.rc (g.dst t) none })
        | some rc' => (false, { h with rc := set h.rc (g.dst t) (some rc') })
    else (false, h)

structure Layout (objects fields : Nat) where
  tag : Fin objects → UInt8 := fun _ => 0
  slots : Fin objects → List (Option (Fin fields))
  count : Fin objects → USize
  closure : Fin objects → Option (Fin fields) := fun _ => none
  value : Fin objects → Option (Fin fields) := fun _ => none

/--
Counts measure physical slots, including nulls and immediates. Present slots enumerate each owned
occurrence in graph order. Thunks use their separate closure and value slots, in that order.
-/
def Layout.Valid (l : Layout objects fields) (g : Graph α objects roots fields) : Prop :=
  (∀ o, (l.count o).toNat = (l.slots o).length) ∧
  (∀ o, l.tag o ≠ 251 → (l.slots o).filterMap id = g.children o) ∧
  ∀ o, l.tag o = 251 → (l.closure o).toList ++ (l.value o).toList = g.children o

/-- Exact physical counts exclude machine-size wraparound. -/
theorem Layout.Valid.slots_length_lt {l : Layout objects fields}
    {g : Graph α objects roots fields} (hl : l.Valid g) (o : Fin objects) :
    (l.slots o).length < USize.size := by
  rw [← hl.1 o]
  exact (l.count o).toNat_lt_size

def adapter (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) :
    Lean.Runtime.GC.Adapter (StateM (Heap objects roots fields))
      (Option (Token roots fields)) (Fin objects) (List (Option (Fin fields)))
      (List (Fin objects)) :=
  { isIgnored := Option.isNone
    object := fun r => r.elim fallback g.dst
    releaseLast := countStep g
    writeNext := fun o todo h => ((), { h with next := fun p => if p = o then todo else h.next p })
    work := fun o h => (o :: h.next o, h)
    readTag := fun o => pure (l.tag o)
    fieldCount := fun o _ => pure (l.count o)
    fieldBegin := fun o _ => pure (l.slots o)
    fieldNext := List.tail
    readField := fun fs => pure (fs.head?.join.map Token.field)
    readThunkClosure := fun o => pure ((l.closure o).map Token.field)
    readThunkValue := fun o => pure ((l.value o).map Token.field)
    dispose := fun o _ h => ((), { h with freed := o :: h.freed })
    empty := [], isEmpty := List.isEmpty, head := (·.headD fallback), tail := fun q => pure q.tail }

theorem countStep_refines (g : Graph α objects roots fields) (h : Heap objects roots fields)
    (todo : List (Fin objects)) (r : Option (Token roots fields)) (fallback : Fin objects) :
    let (last, h') := (countStep g r).run h
    h'.state (if last then r.elim fallback g.dst :: todo else todo) =
      dropRef g (h.state todo) r := by
  cases r with
  | none => rfl
  | some t =>
    by_cases ht : t ∈ h.own
    · cases hr : h.rc (g.dst t) with
      | none => simp [countStep, StateT.run, dropRef, Heap.state, drop, ht, hr]
      | some rc =>
        cases hd : decRef rc <;>
          simp [countStep, StateT.run, releaseCount_refines, dropRef, Heap.state,
            drop, ht, hr, hd]
    · simp [countStep, StateT.run, dropRef, Heap.state, drop, ht]

theorem release_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) (h : Heap objects roots fields) (todo : List (Fin objects))
    (r : Option (Token roots fields)) :
    project ((Lean.Runtime.GC.release (adapter g l fallback) r todo).run h) =
      dropRef g (h.state todo) r := by
  cases r with
  | none => rfl
  | some t =>
    have hc := countStep_refines g h todo (some t) fallback
    simp only [StateT.run] at hc
    generalize hs : countStep g (some t) h = result at hc
    cases result with
    | mk last h' =>
      cases last <;>
        simpa only [Lean.Runtime.GC.release, adapter, Option.isNone_some, Bool.false_eq_true,
          ↓reduceIte, StateT.run, bind, StateT.bind, pure, StateT.pure,
          Option.elim_some, hs, Bool.true_eq_false, project, Heap.state] using hc

theorem releaseField_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) (h : Heap objects roots fields) (todo : List (Fin objects))
    (f : Option (Fin fields)) (fs : List (Option (Fin fields))) :
    project ((Lean.Runtime.GC.releaseField (adapter g l fallback) (f :: fs) todo).run h) =
      dropRef g (h.state todo) (f.map Token.field) := by
  simpa only [Lean.Runtime.GC.releaseField, adapter, List.head?_cons, Option.join_some,
    pure_bind] using release_refines g l fallback h todo (f.map Token.field)

theorem scan_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) (h : Heap objects roots fields) (todo : List (Fin objects))
    (fs : List (Option (Fin fields))) (n : USize) (hn : n.toNat = fs.length) :
    project ((Lean.Runtime.GC.scan List.tail
      (Lean.Runtime.GC.releaseField (adapter g l fallback)) n fs todo).run h) =
      scan g (h.state todo) (fs.filterMap id) := by
  induction fs generalizing h todo n with
  | nil =>
    have hz : n = 0 := USize.toNat_inj.mp (by simpa using hn)
    subst n
    rw [Lean.Runtime.GC.scan]
    rfl
  | cons f fs ih =>
    have hnz : n ≠ 0 := by intro hz; simp [hz] at hn
    have hn' : (n - 1).toNat = fs.length := by
      rw [USize.toNat_sub_of_le]
      · simp only [USize.toNat_one, List.length_cons] at *
        omega
      · apply USize.le_iff_toNat_le.mpr
        simp only [USize.toNat_one, List.length_cons] at *
        omega
    rw [Lean.Runtime.GC.scan]
    simp only [hnz, ↓reduceDIte, StateT.run_bind]
    cases hr : (Lean.Runtime.GC.releaseField (adapter g l fallback) (f :: fs) todo).run h with
    | mk todo' h' =>
      have hp := releaseField_refines g l fallback h todo f fs
      rw [hr] at hp
      change h'.state todo' = dropRef g (h.state todo) (f.map Token.field) at hp
      change project ((Lean.Runtime.GC.scan List.tail
        (Lean.Runtime.GC.releaseField (adapter g l fallback)) (n - 1) fs todo').run h') = _
      rw [ih h' todo' _ hn', hp]
      cases f <;> rfl

theorem finish_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) (h : Heap objects roots fields) (todo : List (Fin objects))
    (o : Fin objects) (tag : UInt8) :
    project ((Lean.Runtime.GC.finish (adapter g l fallback) o tag todo).run h) =
      { h.state todo with freed := o :: h.freed } := by
  rfl

theorem visit_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) (h : Heap objects roots fields) (todo : List (Fin objects))
    (o : Fin objects) (n : USize) (hn : n.toNat = (l.slots o).length)
    (hf : (l.slots o).filterMap id = g.children o) :
    project ((Lean.Runtime.GC.visit List.tail (Lean.Runtime.GC.releaseField (adapter g l fallback))
      (Lean.Runtime.GC.finish (adapter g l fallback) o (l.tag o)) n (l.slots o) todo).run h) =
      visit g (h.state todo) o := by
  rw [Lean.Runtime.GC.visit, StateT.run_bind]
  cases hs : (Lean.Runtime.GC.scan List.tail (Lean.Runtime.GC.releaseField (adapter g l fallback))
      n (l.slots o) todo).run h with
  | mk todo' h' =>
    have hp := scan_refines g l fallback h todo (l.slots o) n hn
    rw [hs, hf] at hp
    change h'.state todo' = scan g (h.state todo) (g.children o) at hp
    change project ((Lean.Runtime.GC.finish (adapter g l fallback) o (l.tag o) todo').run h') = _
    rw [finish_refines]
    change { h'.state todo' with freed := o :: (h'.state todo').freed } = _
    rw [hp]
    rfl

private theorem dropRef_field (g : Graph α objects roots fields) (s : State objects roots fields)
    (f : Option (Fin fields)) :
    dropRef g s (f.map Token.field) = scan g s f.toList := by
  cases f <;> rfl

theorem visitThunk_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (hl : l.Valid g) (fallback : Fin objects) (h : Heap objects roots fields)
    (todo : List (Fin objects)) (o : Fin objects) (ht : l.tag o = 251) :
    project ((Lean.Runtime.GC.visitThunk (adapter g l fallback) o todo).run h) =
      visit g (h.state todo) o := by
  change project ((do
    let todo ← Lean.Runtime.GC.release (adapter g l fallback)
      ((l.closure o).map Token.field) todo
    let todo ← Lean.Runtime.GC.release (adapter g l fallback)
      ((l.value o).map Token.field) todo
    Lean.Runtime.GC.finish (adapter g l fallback) o 251 todo).run h) = _
  rw [StateT.run_bind]
  cases hc : (Lean.Runtime.GC.release (adapter g l fallback)
      ((l.closure o).map Token.field) todo).run h with
  | mk todo' h' =>
    have hp := release_refines g l fallback h todo ((l.closure o).map Token.field)
    rw [hc, dropRef_field] at hp
    change h'.state todo' = scan g (h.state todo) (l.closure o).toList at hp
    change project ((do
      let todo ← Lean.Runtime.GC.release (adapter g l fallback)
        ((l.value o).map Token.field) todo'
      Lean.Runtime.GC.finish (adapter g l fallback) o 251 todo).run h') = _
    rw [StateT.run_bind]
    cases hv : (Lean.Runtime.GC.release (adapter g l fallback)
        ((l.value o).map Token.field) todo').run h' with
    | mk todo'' h'' =>
      have hq := release_refines g l fallback h' todo' ((l.value o).map Token.field)
      rw [hv, dropRef_field] at hq
      change h''.state todo'' = scan g (h'.state todo') (l.value o).toList at hq
      change project
        ((Lean.Runtime.GC.finish (adapter g l fallback) o 251 todo'').run h'') = _
      rw [finish_refines]
      change { h''.state todo'' with freed := o :: (h''.state todo'').freed } = _
      rw [hq, hp]
      simp only [visit, ← hl.2.2 o ht, scan, List.foldl_append]

/-- View a worklist through the driver with direct single-child continuation. -/
def runLoop (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) (todo : List (Fin objects)) :
    StateM (Heap objects roots fields) (List (Fin objects)) :=
  match todo with
  | [] => pure []
  | o :: pending => Lean.Runtime.GC.loop (adapter g l fallback) o pending

private theorem runLoop_resume (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) (todo : List (Fin objects)) :
    (do
      let a := adapter g l fallback
      if a.isEmpty todo then pure todo
      else
        let next ← a.tail todo
        Lean.Runtime.GC.loop a (a.head todo) next) = runLoop g l fallback todo := by
  cases todo <;> rfl

private theorem runLoop_cons (g : Graph α objects roots fields) (l : Layout objects fields)
    (fallback : Fin objects) (o : Fin objects) (todo : List (Fin objects)) :
    runLoop g l fallback (o :: todo) = (do
      let a := adapter g l fallback
      if l.tag o ≤ 243 then
        if l.count o == 1 then
          let r := (l.slots o).head?.join.map Token.field
          if r.isNone then
            let todo ← Lean.Runtime.GC.finish a o (l.tag o) todo
            runLoop g l fallback todo
          else if ← countStep g r then
            a.dispose o (l.tag o)
            runLoop g l fallback (r.elim fallback g.dst :: todo)
          else
            let todo ← Lean.Runtime.GC.finish a o (l.tag o) todo
            runLoop g l fallback todo
        else
          let todo ← Lean.Runtime.GC.visit List.tail (Lean.Runtime.GC.releaseField a)
            (Lean.Runtime.GC.finish a o (l.tag o)) (l.count o) (l.slots o) todo
          runLoop g l fallback todo
      else
        let todo ← if l.tag o == 251 then Lean.Runtime.GC.visitThunk a o todo else
          Lean.Runtime.GC.visit List.tail (Lean.Runtime.GC.releaseField a)
            (Lean.Runtime.GC.finish a o (l.tag o)) (l.count o) (l.slots o) todo
        runLoop g l fallback todo) := by
  rw [runLoop, Lean.Runtime.GC.loop.eq_def]
  simp only [runLoop_resume]
  by_cases hc : l.tag o ≤ 243
  · have ht : l.tag o ≠ 251 := by intro hbad; simp [hbad] at hc
    simp [adapter, hc, ht, runLoop]
  · by_cases ht : l.tag o = 251 <;>
      simp [adapter, hc, ht] <;> rfl

theorem loop_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (hl : l.Valid g) (fallback : Fin objects) (s : State objects roots fields) :
    ∀ (h : Heap objects roots fields) (todo : List (Fin objects)), h.state todo = s →
      project ((runLoop g l fallback todo).run h) = drain g s := by
  fun_induction drain g s with
  | case1 s hs =>
    intro h todo heq
    have ht : todo = [] := by simpa [← heq, Heap.state] using hs
    subst todo
    exact heq
  | case2 s o pending hs ih =>
    intro h todo heq
    have ht : todo = o :: pending := by simpa [← heq, Heap.state] using hs
    subst todo
    have heq' : h.state pending = { s with todo := pending } := by
      rw [← heq]
      rfl
    rw [runLoop_cons]
    by_cases htag : l.tag o ≤ 243
    · have hnth : l.tag o ≠ 251 := by intro hbad; simp [hbad] at htag
      simp only [htag, ↓reduceIte]
      by_cases hn : l.count o = 1
      · have hlen : (l.slots o).length = 1 := by simpa [hn] using (hl.1 o).symm
        obtain ⟨f, hfs⟩ := List.length_eq_one_iff.mp hlen
        have hchildren : f.toList = g.children o := by
          have hc := hl.2.1 o hnth
          rw [hfs] at hc
          cases f <;> simpa [List.filterMap] using hc
        simp only [beq_iff_eq, hn, ↓reduceIte, hfs, List.head?_cons, Option.join_some]
        cases f with
        | none =>
          change project ((runLoop g l fallback pending).run
            { h with freed := o :: h.freed }) = _
          apply ih
          change { h.state pending with freed := o :: (h.state pending).freed } = _
          rw [heq', visit, ← hchildren]
          rfl
        | some f =>
          simp only [Option.map_some, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind]
          cases hr : (countStep g (some (.field f))).run h with
          | mk last h' =>
            have hp := countStep_refines g h pending (some (.field f)) fallback
            rw [hr] at hp
            cases last <;>
              simp only [StateT.run, bind, StateT.bind, pure, StateT.pure,
                Lean.Runtime.GC.finish, adapter, Option.elim_some, Bool.false_eq_true,
                ↓reduceIte] <;>
              apply ih
            all_goals
              change h'.state _ = drop g (h.state pending) (.field f) at hp
              rw [heq'] at hp
              rw [visit, ← hchildren]
              exact congrArg (fun s => { s with freed := o :: s.freed }) hp
      · simp only [beq_iff_eq, hn, ↓reduceIte, StateT.run_bind]
        cases hr : (Lean.Runtime.GC.visit List.tail
            (Lean.Runtime.GC.releaseField (adapter g l fallback))
            (Lean.Runtime.GC.finish (adapter g l fallback) o (l.tag o))
            (l.count o) (l.slots o) pending).run h with
        | mk todo' h' =>
          have hp := visit_refines g l fallback h pending o _ (hl.1 o) (hl.2.1 o hnth)
          rw [hr] at hp
          rw [heq'] at hp
          exact ih h' todo' hp
    · simp only [htag, ↓reduceIte]
      by_cases ht : l.tag o = 251
      · simp only [beq_iff_eq, ht, ↓reduceIte, StateT.run_bind]
        cases hr : (Lean.Runtime.GC.visitThunk (adapter g l fallback) o pending).run h with
        | mk todo' h' =>
          have hp := visitThunk_refines g l hl fallback h pending o ht
          rw [hr, heq'] at hp
          exact ih h' todo' hp
      · simp only [beq_iff_eq, ht, ↓reduceIte, StateT.run_bind]
        cases hr : (Lean.Runtime.GC.visit List.tail
            (Lean.Runtime.GC.releaseField (adapter g l fallback))
            (Lean.Runtime.GC.finish (adapter g l fallback) o (l.tag o))
            (l.count o) (l.slots o) pending).run h with
        | mk todo' h' =>
          have hp := visit_refines g l fallback h pending o _ (hl.1 o) (hl.2.1 o ht)
          rw [hr, heq'] at hp
          exact ih h' todo' hp

/-- Root release and traversal use the same entry point that is exported by the native wrapper. -/
def collect (g : Graph α objects roots fields) (l : Layout objects fields)
    (s : State objects roots fields) (d : Fin roots) : State objects roots fields :=
  project ((Lean.Runtime.GC.decRefCold (adapter g l (g.root d)) (some (.root d))).run
    (Heap.ofState s))

/-- The whole shared entry point terminates and agrees with the ownership collector. -/
theorem entry_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (hl : l.Valid g) (fallback : Fin objects) (h : Heap objects roots fields)
    (t : Token roots fields) :
    project ((Lean.Runtime.GC.decRefCold (adapter g l fallback) (some t)).run h) =
      drain g (drop g (h.state []) t) := by
  have hc := countStep_refines g h [] (some t) fallback
  simp only [StateT.run] at hc
  generalize hs : countStep g (some t) h = result at hc
  cases result with
  | mk last h' =>
    have step : (Lean.Runtime.GC.decRefCold (adapter g l fallback) (some t)).run h =
        (runLoop g l fallback (if last then [g.dst t] else [])).run h' := by
      cases last <;>
        simp only [Lean.Runtime.GC.decRefCold, adapter, StateT.run, bind, StateT.bind,
          hs, Bool.false_eq_true, ↓reduceIte, runLoop, Option.elim_some]
    rw [step, loop_refines g l hl fallback _ h' _ rfl]
    exact congrArg (drain g) hc

theorem collect_refines (g : Graph α objects roots fields) (l : Layout objects fields)
    (hl : l.Valid g) (s : State objects roots fields) (hs : s.todo = []) (d : Fin roots) :
    collect g l s d = drain g (drop g s (.root d)) := by
  have heq : (Heap.ofState s).state [] = s := by cases s; simp_all [Heap.ofState, Heap.state]
  simp only [collect, entry_refines g l hl, heq]

/--
The shared collector releases root `d` as `Released` says, and every other schedule run until no
step applies ends in the same state, up to the order of reclamation.
-/
theorem collect_released {g : Graph α objects roots fields} (l : Layout objects fields)
    (hl : l.Valid g) {s : State objects roots fields} (hs : Quiescent g s) (d : Fin roots) :
    Released g s d (collect g l s d) ∧
      ∀ a, Steps g (drop g s (.root d)) a → Stuck g a → Equiv a (collect g l s d) := by
  rw [collect_refines g l hl s hs.todo]
  exact drain_released hs d

end RcGraph

namespace Lean.Runtime.GC

/--
Bind the exported wrapper to the shared entry point and the selected opaque native primitives.
Changing the wrapper or swapping a primitive breaks this equality independently of the graph proof.
-/
theorem native_entry_uses_shared (o : USize) :
    Native.decRefCold o = (do
      let _ ← decRefCold
        { isIgnored := fun r => r == 0 || r &&& 1 != 0
          object := id
          releaseLast := fun r => releaseLast (Native.readRC r) (Native.writeRC r)
            (Native.fetchAddRC r)
          writeNext := Native.writeNext, work := pure
          readTag := Native.readTag, fieldCount := Native.fieldCount
          fieldBegin := Native.fieldBegin, fieldNext := Native.fieldNext
          readField := Native.readField
          readThunkClosure := Native.readThunkClosure, readThunkValue := Native.readThunkValue
          dispose := Native.dispose
          empty := 0, isEmpty := (· == 0), head := id, tail := Native.readNext } o
      pure ()) := by
  simp only [Native.decRefCold, Native.adapter, Bool.or_comm]

end Lean.Runtime.GC
