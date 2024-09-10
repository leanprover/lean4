def filter (p : α → Prop) [inst : DecidablePred p] (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' =>
    if p x then
      -- Trying to confuse `omega` by creating subterms that are structurally different
      -- but definitionally equal.
      x :: @filter α p (fun x => inst x) xs'
    else
      @filter α p inst xs'

def filter_length (p : α → Prop) [DecidablePred p] : (filter p xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    simp only [filter]
    split <;> simp only [List.length] <;> omega

inductive Op where
  | bla
  | foo (a : Nat)

def Op.ctorIdx : Op → Nat
  | .bla => 0
  | .foo .. => 1

def Op.fooData (o : Op) (h : o.ctorIdx = 1) : Nat :=
  match o, h with
  | .foo a, _ => a

theorem ex (o₁ o₂ o₃ : Op)
    (h₁ : o₁.ctorIdx = 1)
    (h₂ : o₁.ctorIdx = o₂.ctorIdx)
    (h₃ : o₂.ctorIdx = o₃.ctorIdx)
    (h₄ : o₂.ctorIdx = 1)
    (_ : o₁.fooData h₁ < o₂.fooData h₄)
    (_ : o₂.fooData (h₂ ▸ h₁) < o₃.fooData (h₃ ▸ h₄))
    : o₁.fooData h₁ < o₃.fooData (h₃ ▸ h₄) := by
  omega
