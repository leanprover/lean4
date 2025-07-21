set_option warn.sorry false

structure Vec α n where
  toList : List α
  length_toList : toList.length = n

-- We need the property to be parametric

theorem Vec.prop_parametric (xs : Vec α n) :
    (xs.toList.map f).length = n := by
  have := xs.length_toList
  grind

-- Ok, cannot changes indices in nested occurrences

/--
error: (kernel) invalid nested inductive datatype 'Eq', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
structure VTree n where
  node : Vec (VTree (n-1)) n

/--
error: (kernel) invalid nested inductive datatype 'List', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive VTree.Raw : Nat → Type where
  | mk : List (VTree.Raw (n-1)) → VTree.Raw n


/--
error: (kernel) invalid nested inductive datatype 'Eq', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive Tree3' where
  | leaf : Tree3'
  | node : Vec Tree3' 3 → Tree3'

inductive Tree3.Raw where
  | leaf : Tree3.Raw
  | node : List Tree3.Raw → Tree3.Raw

-- TODO: Can we use `Tree3.Raw.below` for this?
mutual
def Tree3.WF (t : Tree3.Raw) : Prop :=
  match t with
  | .leaf => True
  | .node xs => xs.length = 3 ∧ Tree3.WF_aux1 xs
termination_by structural t

def Tree3.WF_aux1 (xs : List Tree3.Raw) : Prop :=
  match xs with
  | [] => True
  | x::xs => Tree3.WF x ∧ Tree3.WF_aux1 xs
termination_by structural xs
end

def Tree3 := { t : Tree3.Raw // Tree3.WF t }

/-- Fake constructor -/
def Tree3.leaf : Tree3 where
  val := .leaf
  property := True.intro

def Tree3.node (xs : Vec Tree3 3) : Tree3 where
  val := .node (xs.toList.map (·.val))
  property := ⟨xs.prop_parametric, sorry⟩

-- At this point, I feel again nudged towards a more abstract view of
-- the container type, to keep the encoding somewhat sane

#exit

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
