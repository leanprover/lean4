def List.foldl_wf [SizeOf β] (bs : List β) (init : α) (f : α → (b : β) → sizeOf b < sizeOf bs → α) : α :=
  go init bs (Nat.le_refl ..)
where
  go (a : α) (cs : List β) (h : sizeOf cs ≤ sizeOf bs) : α :=
    match cs with
    | [] => a
    | c :: cs =>
      have : sizeOf c < sizeOf (c :: cs) := by simp +arith
      -- TODO: simplify using linarith
      have h₁ : sizeOf c < sizeOf bs := Nat.lt_of_lt_of_le this h
      have : sizeOf cs + (sizeOf c + 1) = sizeOf c + sizeOf cs + 1 := by simp +arith
      have : sizeOf cs ≤ sizeOf c + sizeOf cs + 1 := by rw [← this]; apply Nat.le_add_right
      have h₂ : sizeOf cs ≤ sizeOf bs := by simp +arith at h; apply Nat.le_trans this h
      go (f a c h₁) cs h₂

theorem List.foldl_wf_eq [SizeOf β] (bs : List β) (init : α) (f : α → β → α) : bs.foldl_wf init (fun a b _ => f a b) = bs.foldl f init := by
  simp [List.foldl_wf]
  have : (a : α) → (cs : List β) → (h : sizeOf cs ≤ sizeOf bs) → foldl_wf.go bs (fun a b _ => f a b) a cs h = cs.foldl f a := by
    intro a cs h
    induction cs generalizing a with simp [List.foldl_wf.go, List.foldl]
    | cons c cs ih => simp [ih]
  exact this init bs (Nat.le_refl ..)

inductive Expr where
  | app (f : String) (args : List Expr)
  | var (n : String)

-- TODO: `WF.lean` should replace `List.foldl` with `List.foldl_wf`, and then apply `List.foldl_wf_eq` when proving equation theorems.
@[simp] def Expr.numVars : Expr → Nat
  | app f args => args.foldl_wf 0 fun sum arg h =>
    -- TODO: linarith should prove the following proposition
    -- TODO: decreasing_tactic should invoke `linarith`
    have : sizeOf arg < 1 + sizeOf f + sizeOf args := Nat.lt_of_lt_of_le h (Nat.le_add_left ..)
    sum + numVars arg
  | var _ => 1

/-
  TODO: we should have a new attribute for registering theorems such as `List.foldl_wf_eq` and `List.map_foldl_wf_eq`
  Here is the steps missing in the `WF` module.
  1- Replace functions such as `List.foldl` with their `_wf` version. Note that the new hypothesis is unused.
  2- Use the current `WF` implementation. The `decreasing_tactic` must invoke `linarith` to be able to discharge the goals.
  3- When generating equation lemmas, we first prove that the defined function is equal to the RHS containing the `_wf` function,
     and then apply `_wf_eq` simp theorem to simplify.
-/

-- Example for step 3
theorem Expr.numVars_app_eq (f : String) (args : List Expr) : (Expr.app f args).numVars = args.foldl (fun sum arg => sum + arg.numVars) 0 := by
  simp [numVars, List.foldl_wf_eq]

#guard (Expr.app "f" [Expr.var "a", Expr.app "g" [Expr.var "b", Expr.var "c"]] |>.numVars) == 3

def List.map_wf [SizeOf α] (as : List α) (f : (a : α) → sizeOf a < sizeOf as → β) : List β :=
  go as (Nat.le_refl ..)
where
  go (cs : List α) (h : sizeOf cs ≤ sizeOf as) : List β :=
    match cs with
    | [] => []
    | c :: cs =>
      have : sizeOf c < sizeOf (c :: cs) := by simp +arith
      -- TODO: simplify using linarith
      have h₁ : sizeOf c < sizeOf as := Nat.lt_of_lt_of_le this h
      have : sizeOf cs + (sizeOf c + 1) = sizeOf c + sizeOf cs + 1 := by simp +arith
      have : sizeOf cs ≤ sizeOf c + sizeOf cs + 1 := by rw [← this]; apply Nat.le_add_right
      have h₂ : sizeOf cs ≤ sizeOf as := by simp +arith at h; apply Nat.le_trans this h
      f c h₁ :: go cs h₂

theorem List.map_wf_eq [SizeOf α] (as : List α) (f : α → β) : as.map_wf (fun a _ => f a) = as.map f := by
  simp [List.map_wf]
  have : (cs : List α) → (h : sizeOf cs ≤ sizeOf as) → map_wf.go as (fun a _ => f a) cs h = cs.map f := by
    intro cs h
    induction cs with simp [List.map_wf.go, List.map]
    | cons c cs ih => simp [ih]
  exact this as (Nat.le_refl ..)
