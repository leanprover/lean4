attribute [-instance] List.instOrd

class POrd {α} (x y : α) where
  pord : Ordering

instance instPOrdList [∀ x y, @POrd α x y] : ∀ (xs ys : List α), @POrd (List α) xs ys
  | [], [] => ⟨.eq⟩
  | [], _::__ => ⟨.lt⟩
  | _::_, [] => ⟨.lt⟩
  | x::xs, y::ys =>
    letI := instPOrdList xs ys
    ⟨ (POrd.pord x y).then (POrd.pord xs ys) ⟩

-- Now the setup for wf_preprocess

def instPOrdList_attach : ∀ (xs ys : List α), (∀ x y, x ∈ xs → y ∈ ys → @POrd α x y) →
    @POrd (List α) xs ys
  | [], [], _ => ⟨.eq⟩
  | [], _::__, _ => ⟨.lt⟩
  | _::_, [], _ => ⟨.lt⟩
  | x::xs, y::ys, f =>
    ⟨ (f x y List.mem_cons_self List.mem_cons_self).pord.then
      (instPOrdList_attach xs ys (fun x y hx hy => f x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy))).pord
    ⟩

@[wf_preprocess]
theorem instPOrdList_wfParam (f : ∀ x y, @POrd α x y) : ∀ (xs ys : List α),
   @instPOrdList _ f xs ys = instPOrdList_attach xs ys (fun x y _ _ => f x y) := by
  intros xs ys
  fun_induction instPOrdList <;> grind [instPOrdList_attach]

-- An inductive type nesting through lists

-- set_option trace.Elab.Deriving.ord true
inductive T where
  | node : List T → T
-- deriving Ord

-- The recursive instance works

instance instPOrdT : (xs : T) → (ys : T) → @POrd T xs ys
  | .node xs, .node ys =>
    ⟨@POrd.pord _ xs ys (@instPOrdList _ (fun x y => instPOrdT x y) _ _)⟩

-- Connection to Ord

def instPOrd_of_ord {α} [Ord α] (x y : α) : @POrd α x y := ⟨Ord.compare x y⟩
-- def instOrd_of_pord {α} [∀ (x y : α), POrd x y] : @Ord α := ⟨fun x y => POrd.pord x y⟩

-- attribute [local instance] instPOrd_of_ord in
-- instance [Ord α] : Ord (List α) where
  -- compare x y := POrd.pord x y

instance : Ord T where
  compare x y := POrd.pord x y

theorem T.ordSpec : compare (T.node xs) (T.node ys) = compare xs ys := by
  simp [compare, POrd.pord, instPOrdT]

attribute [instance] List.instOrd

def List.compare_of_compare : ∀ (xs ys : List α), (compare : ∀ x y, x ∈ xs → y ∈ ys → Ordering) →
    Ordering
  | [], [], _ => .eq
  | [], _::__, _ => .lt
  | _::_, [], _ => .gt
  | x::xs, y::ys, f =>
    (f x y List.mem_cons_self List.mem_cons_self).then
      (List.compare_of_compare xs ys (fun x y hx hy => f x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)))

@[wf_preprocess]
theorem List.instOrd_compare_wfParam (i : Ord α) : ∀ (xs ys : List α),
   (@List.instOrd _ i).compare (wfParam xs) ys =
    List.compare_of_compare xs ys (fun x y _ _ => i.compare x y) := by
  intros xs ys
  induction xs generalizing ys
  · cases ys
    · simp [Ord.compare, List.compareLex, wfParam, List.compare_of_compare]
    · simp [Ord.compare, List.compareLex, wfParam, List.compare_of_compare]
  · cases ys
    · simp [Ord.compare, List.compareLex, wfParam, List.compare_of_compare]
    · simp [Ord.compare, List.compareLex, wfParam, List.compare_of_compare, *]
      split <;> simp_all
      sorry

@[wf_preprocess]
theorem Ord.compare_mk {f : α → α → Ordering} : @Ord.compare _ (Ord.mk f) = f := rfl

-- @[wf_preprocess]
-- theorem Ord.compare_mk' {f : α → α → Ordering} : @Ord.compare _ (Ord.mk f) x y = f x y := rfl

-- Why does it not beta-reduce here?

set_option trace.Elab.definition.wf true in
def T.compare : (xs : T) → (ys : T) → Ordering
  | .node xs, .node ys =>
    letI : Ord T := ⟨T.compare⟩
    Ord.compare xs ys
termination_by xs => xs
