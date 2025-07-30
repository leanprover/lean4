set_option pp.sanitizeNames false
set_option trace.Elab.Deriving.ord true

inductive T where
  | node : List T → T
deriving Ord

def List.compareLex_attached : ∀ (xs ys : List α), (compare : ∀ x y, x ∈ xs → y ∈ ys → Ordering) →
    Ordering
  | [], [], _ => .eq
  | [], _, _ => .lt
  | _, [], _ => .gt
  | x::xs, y::ys, f =>
    (f x y List.mem_cons_self List.mem_cons_self).then
      (List.compareLex_attached xs ys (fun x y hx hy => f x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)))

theorem List.compareLex_wfParam (compare : α → α → Ordering) (xs ys):
  List.compareLex compare (wfParam xs) ys =
    List.compareLex_attached xs ys (fun x y _ _ => compare (wfParam x) y) := by
  dsimp [wfParam]
  fun_induction List.compareLex
  all_goals simp_all [List.compareLex_attached]

@[wf_preprocess]
theorem List.instOrd_compare_wfParam (i : Ord α) : ∀ (xs ys : List α),
   (@List.instOrd _ i).compare (wfParam xs) ys =
    List.compareLex_attached xs ys (fun x y _ _ => i.compare (wfParam x) y) :=
  fun xs ys => List.compareLex_wfParam _ xs ys

def T.compare : (xs : T) → (ys : T) → Ordering
  | .node xs, .node ys =>
    letI : Ord T := ⟨T.compare⟩
    Ordering.then (Ord.compare xs ys) Ordering.eq
termination_by xs => xs
