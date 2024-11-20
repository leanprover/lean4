namespace Std.Range

/-- The number of elements contained in a `Std.Range`. -/
def numElems (r : Range) : Nat :=
  if r.step = 0 then
    -- This is a very weird choice, but it is chosen to coincide with the `forIn` impl
    if r.stop ≤ r.start then 0 else r.stop
  else
    (r.stop - r.start + r.step - 1) / r.step

theorem numElems_stop_le_start : ∀ r : Range, r.stop ≤ r.start → r.numElems = 0 := sorry

private theorem numElems_le_iff {start stop step i} (hstep : 0 < step) :
    (stop - start + step - 1) / step ≤ i ↔ stop ≤ start + step * i :=
  sorry

theorem mem_range'_elems (r : Range) (h : x ∈ List.range' r.start r.numElems r.step) : x ∈ r := by
  sorry

theorem forIn'_eq_forIn_range' [Monad m] (r : Std.Range)
    (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) :
    forIn' r init f =
    forIn
      ((List.range' r.start r.numElems r.step).pmap Subtype.mk fun _ => mem_range'_elems r)
      init (fun ⟨a, h⟩ => f a h) := by
  let ⟨start, stop, step⟩ := r
  let L := List.range' start (numElems ⟨start, stop, step⟩) step
  let f' : { a // start ≤ a ∧ a < stop } → _ := fun ⟨a, h⟩ => f a h
  suffices ∀ H, forIn' [start:stop:step] init f = forIn (L.pmap Subtype.mk H) init f' from this _
  intro H; dsimp only [forIn', Range.forIn']
  if h : start < stop then
    simp [numElems, Nat.not_le.2 h, L]; split
    · subst step
      suffices ∀ n H init,
          forIn'.loop start stop 0 f n start (Nat.le_refl _) init =
          forIn ((List.range' start n 0).pmap Subtype.mk H) init f' from this _ ..
      intro n; induction n with (intro H init; unfold forIn'.loop; simp [*]) -- fails here, can't unfold
      | succ n ih => simp [ih (List.forall_mem_cons.1 H).2]; rfl
    · next step0 =>
      have hstep := Nat.pos_of_ne_zero step0
      suffices ∀ fuel l i hle H, l ≤ fuel →
          (∀ j, stop ≤ i + step * j ↔ l ≤ j) → ∀ init,
          forIn'.loop start stop step f fuel i hle init =
          forIn ((List.range' i l step).pmap Subtype.mk H) init f' by
        refine this _ _ _ _ _
          ((numElems_le_iff hstep).2 (Nat.le_trans ?_ (Nat.le_add_left ..)))
          (fun _ => (numElems_le_iff hstep).symm) _
        conv => lhs; rw [← Nat.one_mul stop]
        exact Nat.mul_le_mul_right stop hstep
      intro fuel; induction fuel with intro l i hle H h1 h2 init
      | zero => simp [forIn'.loop, Nat.le_zero.1 h1]
      | succ fuel ih =>
        cases l with
        | zero => rw [forIn'.loop]; simp [Nat.not_lt.2 <| by simpa using (h2 0).2 (Nat.le_refl _)]
        | succ l =>
          have ih := ih _ _ (Nat.le_trans hle (Nat.le_add_right ..))
            (List.forall_mem_cons.1 H).2 (Nat.le_of_succ_le_succ h1) fun i => by
              rw [Nat.add_right_comm, Nat.add_assoc, ← Nat.mul_succ, h2, Nat.succ_le_succ_iff]
          have := h2 0; simp at this
          rw [forIn'.loop]; simp [this, ih]; rfl
  else
    simp [List.range', h, numElems_stop_le_start ⟨start, stop, step⟩ (Nat.not_lt.1 h), L]
    cases stop <;> unfold forIn'.loop <;> simp [List.forIn', h]
