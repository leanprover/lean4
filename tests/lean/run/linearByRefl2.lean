abbrev Var := Nat

structure Context where
  vars : List Nat

private def List.getIdx : List α → Nat → α → α
  | [],    i,   u => u
  | a::as, 0,   u => a
  | a::as, i+1, u => getIdx as i u

/--
  When encoding polynomials. We use `fixedVar` for encoding numerals.
  The denotation of `fixedVar` is always `1`. -/
def fixedVar := 100000000 -- Any big number should work here

def Var.denote (ctx : Context) (v : Var) : Nat :=
  if v = fixedVar then 1 else ctx.vars.getIdx v 0

inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mulL (k : Nat) (a : Expr)
  | mulR (a : Expr) (k : Nat)
  deriving Inhabited, Repr

def Expr.denote (ctx : Context) : Expr → Nat
  | Expr.add a b  => Nat.add (denote ctx a) (denote ctx b)
  | Expr.num k    => k
  | Expr.var v    => v.denote ctx
  | Expr.mulL k e => k * denote ctx e
  | Expr.mulR e k => denote ctx e * k

abbrev Poly := List (Nat × Var)

def Poly.denote (ctx : Context) (p : Poly) : Nat :=
  match p with
  | [] => 0
  | (k, v) :: p => k * v.denote ctx + denote ctx p

def Poly.insertSorted (k : Nat) (v : Var) (p : Poly) : Poly :=
  match p with
  | [] => [(k, v)]
  | (k', v') :: p => if v < v' then (k, v) :: (k', v') :: p else (k', v') :: insertSorted k v p

def Poly.sort (p : Poly) : Poly :=
  let rec go (p : Poly) (r : Poly) : Poly :=
    match p with
    | [] => r
    | (k, v) :: p => go p (r.insertSorted k v)
  go p []

def Poly.fuse (p : Poly) : Poly :=
  match p with
  | []  => []
  | (k, v) :: p =>
    match fuse p with
    | [] => [(k, v)]
    | (k', v') :: p' => if v = v' then (k+k', v)::p' else (k, v) :: (k', v') :: p'

def Poly.mul (k : Nat) (p : Poly) : Poly :=
  if k = 0 then
    []
  else if k = 1 then
    p
  else
    go p
where
  go : Poly → Poly
  | [] => []
  | (k', v) :: p => (k*k', v) :: go p

def Poly.cancelAux (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly) : Poly × Poly :=
  match fuel with
  | 0 => (r₁.reverse ++ m₁, r₂.reverse ++ m₂)
  | fuel + 1 =>
    match m₁, m₂ with
    | m₁, [] => (r₁.reverse ++ m₁, r₂.reverse)
    | [], m₂ => (r₁.reverse, r₂.reverse ++ m₂)
    | (k₁, v₁) :: m₁, (k₂, v₂) :: m₂ =>
      if v₁ < v₂ then
        cancelAux fuel m₁ ((k₂, v₂) :: m₂) ((k₁, v₁) :: r₁) r₂
      else if v₁ > v₂ then
        cancelAux fuel ((k₁, v₁) :: m₁) m₂ r₁ ((k₂, v₂) :: r₂)
      else if k₁ < k₂ then
        cancelAux fuel m₁ m₂ r₁ ((k₂ - k₁, v₁) :: r₂)
      else if k₁ > k₂ then
        cancelAux fuel m₁ m₂ ((k₁ - k₂, v₁) :: r₁) r₂
      else
        cancelAux fuel m₁ m₂ r₁ r₂

def Poly.cancel (p₁ p₂ : Poly) : Poly × Poly :=
  cancelAux (p₁.length + p₂.length) p₁ p₂ [] []

def Poly.isNum? (p : Poly) : Option Nat :=
  match p with
  | [] => some 0
  | [(k, v)] => if v = fixedVar then some k else none
  | _ => none

def Poly.isZero (p : Poly) : Bool :=
  p = []

def Poly.isNonZero (p : Poly) : Bool :=
  match p with
  | [] => false
  | (k, v) :: p => if v = fixedVar then k > 0 else isNonZero p

def Poly.denote_eq (ctx : Context) (mp : Poly × Poly) : Prop := mp.1.denote ctx = mp.2.denote ctx

def Poly.denote_le (ctx : Context) (mp : Poly × Poly) : Prop := mp.1.denote ctx ≤ mp.2.denote ctx

def Expr.toPoly : Expr → Poly
  | Expr.num k    => if k = 0 then [] else [ (k, fixedVar) ]
  | Expr.var i    => [(1, i)]
  | Expr.add a b  => a.toPoly ++ b.toPoly
  | Expr.mulL k a => a.toPoly.mul k
  | Expr.mulR a k => a.toPoly.mul k

def Expr.toNormPoly (e : Expr) : Poly :=
  e.toPoly.sort.fuse

def Expr.inc (e : Expr) : Expr :=
   Expr.add e (Expr.num 1)

structure PolyCnstr  where
  eq  : Bool
  lhs : Poly
  rhs : Poly

def PolyCnstr.mul (k : Nat) (c : PolyCnstr) : PolyCnstr :=
  { c with lhs := c.lhs.mul k, rhs := c.rhs.mul k }

def PolyCnstr.combine (c₁ c₂ : PolyCnstr) : PolyCnstr :=
  let (lhs, rhs) := Poly.cancel (c₁.lhs ++ c₂.lhs).sort.fuse (c₁.rhs ++ c₂.rhs).sort.fuse
  { eq := c₁.eq && c₂.eq, lhs, rhs }

structure ExprCnstr where
  eq  : Bool
  lhs : Expr
  rhs : Expr

def PolyCnstr.denote (ctx : Context) (c : PolyCnstr) : Prop :=
  if c.eq then
    Poly.denote_eq ctx (c.lhs, c.rhs)
  else
    Poly.denote_le ctx (c.lhs, c.rhs)

def PolyCnstr.norm (c : PolyCnstr) : PolyCnstr :=
  let (lhs, rhs) := Poly.cancel c.lhs.sort.fuse c.rhs.sort.fuse
  { eq := c.eq, lhs, rhs }

def PolyCnstr.isUnsat (c : PolyCnstr) : Bool :=
  if c.eq then
    (c.lhs.isZero && c.rhs.isNonZero) || (c.lhs.isNonZero && c.rhs.isZero)
  else
    c.lhs.isNonZero && c.rhs.isZero

def PolyCnstr.isValid (c : PolyCnstr) : Bool :=
  if c.eq then
    c.lhs.isZero && c.rhs.isZero
  else
    c.lhs.isZero

def ExprCnstr.denote (ctx : Context) (c : ExprCnstr) : Prop :=
  if c.eq then
    c.lhs.denote ctx = c.rhs.denote ctx
  else
    c.lhs.denote ctx ≤ c.rhs.denote ctx

def ExprCnstr.toPoly (c : ExprCnstr) : PolyCnstr :=
  let (lhs, rhs) := Poly.cancel c.lhs.toNormPoly c.rhs.toNormPoly
  { c with lhs, rhs }

abbrev Certificate := List (Nat × ExprCnstr)

def Certificate.combineHyps (c : PolyCnstr) (hs : Certificate) : PolyCnstr :=
  match hs with
  | [] => c
  | (k, c') :: hs => combineHyps (PolyCnstr.combine c (c'.toPoly.mul (k+1))) hs

def Certificate.combine (hs : Certificate) : PolyCnstr :=
  match hs with
  | [] => { eq := true, lhs := [], rhs := [] }
  | (k, c) :: hs => combineHyps (c.toPoly.mul (k+1)) hs

def Certificate.denote (ctx : Context) (c : Certificate) : Prop :=
  match c with
  | [] => False
  | (_, c)::hs => c.denote ctx → denote ctx hs

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.right_distrib Nat.left_distrib Nat.mul_assoc Nat.mul_comm

attribute [local simp] Poly.denote Expr.denote Poly.insertSorted Poly.sort Poly.sort.go Poly.fuse Poly.cancelAux
attribute [local simp] Poly.mul Poly.mul.go

theorem Poly.denote_insertSorted (ctx : Context) (k : Nat) (v : Var) (p : Poly) : (p.insertSorted k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  match p with
  | [] => simp
  | (k', v') :: p => by_cases h : v < v' <;> simp [h, denote_insertSorted]

attribute [local simp] Poly.denote_insertSorted

theorem Poly.denote_sort_go (ctx : Context) (p : Poly) (r : Poly) : (sort.go p r).denote ctx = p.denote ctx + r.denote ctx := by
  match p with
  | [] => simp
  | (k, v):: p => simp [denote_sort_go]

attribute [local simp] Poly.denote_sort_go

theorem Poly.denote_sort (ctx : Context) (m : Poly) : m.sort.denote ctx = m.denote ctx := by
  simp

attribute [local simp] Poly.denote_sort

theorem Poly.denote_append (ctx : Context) (p q : Poly) : (p ++ q).denote ctx = p.denote ctx + q.denote ctx := by
  match p with
  | []  => simp
  | (k, v) :: p => simp [denote_append]

attribute [local simp] Poly.denote_append

theorem Poly.denote_cons (ctx : Context) (k : Nat) (v : Var) (p : Poly) : denote ctx ((k, v) :: p) = k * v.denote ctx + p.denote ctx := by
  match p with
  | []     => simp
  | _ :: m => simp [denote_cons]

attribute [local simp] Poly.denote_cons

theorem Poly.denote_reverseAux (ctx : Context) (p q : Poly) : denote ctx (List.reverseAux p q) = denote ctx (p ++ q) := by
  match p with
  | [] => simp [List.reverseAux]
  | (k, v) :: p => simp [List.reverseAux, denote_reverseAux]

attribute [local simp] Poly.denote_reverseAux

theorem Poly.denote_reverse (ctx : Context) (p : Poly) : denote ctx (List.reverse p) = denote ctx p := by
  simp [List.reverse]

attribute [local simp] Poly.denote_reverse

theorem Poly.denote_fuse (ctx : Context) (p : Poly) : p.fuse.denote ctx = p.denote ctx := by
  match p with
  | [] => rfl
  | (k, v) :: p =>
    have ih := denote_fuse ctx p
    simp
    split
    case _ h => simp [← ih, h]
    case _ k' v' p' h => by_cases he : v = v' <;> simp [he, ← ih, h]

attribute [local simp] Poly.denote_fuse

theorem Poly.denote_mul (ctx : Context) (k : Nat) (p : Poly) : (p.mul k).denote ctx = k * p.denote ctx := by
  simp
  by_cases h : k = 0 <;> simp [h]
  by_cases h : k = 1 <;> simp [h]
  induction p with
  | nil  => simp
  | cons kv m ih => cases kv with | _ k' v => simp [ih]

attribute [local simp] Poly.denote_mul

theorem Poly.denote_eq_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂)) : denote_eq ctx (cancelAux fuel m₁ m₂ r₁ r₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp
    split <;> simp at h <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv]
    . apply ih; simp [denote_eq] at h |-; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv]
      . apply ih; simp [denote_eq] at h |-; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk]
        . apply ih
          simp [denote_eq] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Eq.symm
          apply Nat.sub_eq_of_eq_add
          simp [h]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk]
          . apply ih
            simp [denote_eq] at h |-
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
            apply Nat.sub_eq_of_eq_add
            simp [h]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            apply ih
            simp [denote_eq] at h |-
            rw [← Nat.add_assoc, ← Nat.add_assoc] at h
            exact Nat.add_right_cancel h

theorem Poly.of_denote_eq_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_eq ctx (cancelAux fuel m₁ m₂ r₁ r₂)) : denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp at h
    split at h <;> simp <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv] at h
    . have ih := ih (h := h); simp [denote_eq] at ih ⊢; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv] at h
      . have ih := ih (h := h); simp [denote_eq] at ih ⊢; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk] at h
        . have ih := ih (h := h); simp [denote_eq] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih.symm
          simp at ih
          rw [ih]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk] at h
          . have ih := ih (h := h); simp [denote_eq] at ih ⊢
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
            have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih
            simp at ih
            rw [ih]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            have ih := ih (h := h); simp [denote_eq] at ih ⊢
            rw [← Nat.add_assoc, ih, Nat.add_assoc]

theorem Poly.denote_eq_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_eq ctx (m₁, m₂)) : denote_eq ctx (cancel m₁ m₂) := by
  simp; apply denote_eq_cancelAux; simp [h]

theorem Poly.of_denote_eq_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_eq ctx (cancel m₁ m₂)) : denote_eq ctx (m₁, m₂) := by
  simp at h
  have := Poly.of_denote_eq_cancelAux (h := h)
  simp at this
  assumption

theorem Poly.denote_eq_cancel_eq (ctx : Context) (m₁ m₂ : Poly) : denote_eq ctx (cancel m₁ m₂) = denote_eq ctx (m₁, m₂) :=
  propext <| Iff.intro (fun h => of_denote_eq_cancel h) (fun h => denote_eq_cancel h)

attribute [local simp] Poly.denote_eq_cancel_eq

theorem Poly.denote_le_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_le ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂)) : denote_le ctx (cancelAux fuel m₁ m₂ r₁ r₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp
    split <;> simp at h <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv]
    . apply ih; simp [denote_le] at h |-; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv]
      . apply ih; simp [denote_le] at h |-; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk]
        . apply ih
          simp [denote_le] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Nat.le_sub_of_add_le
          simp [h]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk]
          . apply ih
            simp [denote_le] at h |-
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
            apply Nat.sub_le_of_le_add (Nat.le_trans haux (Nat.le_add_left ..))
            simp [h]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            apply ih
            simp [denote_le] at h |-
            rw [← Nat.add_assoc, ← Nat.add_assoc] at h
            apply Nat.le_of_add_le_add_right h
    done

theorem Poly.of_denote_le_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_le ctx (cancelAux fuel m₁ m₂ r₁ r₂)) : denote_le ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp at h
    split at h <;> simp <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv] at h
    . have ih := ih (h := h); simp [denote_le] at ih ⊢; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv] at h
      . have ih := ih (h := h); simp [denote_le] at ih ⊢; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk] at h
        . have ih := ih (h := h); simp [denote_le] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have := Nat.add_le_of_le_sub (Nat.le_trans haux (Nat.le_add_left ..)) ih
          simp at this
          exact this
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk] at h
          . have ih := ih (h := h); simp [denote_le] at ih ⊢
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
            have := Nat.le_add_of_sub_le (Nat.le_trans haux (Nat.le_add_left ..)) ih
            simp at this
            exact this
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            have ih := ih (h := h); simp [denote_le] at ih ⊢
            have := Nat.add_le_add_right ih (k₁ * Var.denote ctx v₁)
            simp at this
            exact this

theorem Poly.denote_le_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_le ctx (m₁, m₂)) : denote_le ctx (cancel m₁ m₂) := by
  simp; apply denote_le_cancelAux; simp [h]

theorem Poly.of_denote_le_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_le ctx (cancel m₁ m₂)) : denote_le ctx (m₁, m₂) := by
  simp at h
  have := Poly.of_denote_le_cancelAux (h := h)
  simp at this
  assumption

theorem Poly.denote_le_cancel_eq (ctx : Context) (m₁ m₂ : Poly) : denote_le ctx (cancel m₁ m₂) = denote_le ctx (m₁, m₂) :=
  propext <| Iff.intro (fun h => of_denote_le_cancel h) (fun h => denote_le_cancel h)

attribute [local simp] Poly.denote_le_cancel_eq

@[simp] theorem Expr.denote_toPoly (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k => by_cases h : k = 0 <;> simp [toPoly, h, Var.denote]
  | var i => simp [toPoly]
  | add a b iha ihb => simp [toPoly, iha, ihb]
  | mulL k a ih => simp [toPoly, ih, -Poly.mul]
  | mulR k a ih => simp [toPoly, ih, -Poly.mul]

theorem Expr.eq_of_toNormPoly (ctx : Context) (a b : Expr) (h : a.toNormPoly = b.toNormPoly) : a.denote ctx = b.denote ctx := by
  simp [toNormPoly] at h
  have h := congrArg (Poly.denote ctx) h
  simp at h
  assumption

theorem Expr.of_cancel_eq (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.toNormPoly b.toNormPoly = (c.toPoly, d.toPoly)) : (a.denote ctx = b.denote ctx) = (c.denote ctx = d.denote ctx) := by
  have := Poly.denote_eq_cancel_eq ctx a.toNormPoly b.toNormPoly
  rw [h] at this
  simp [toNormPoly, Poly.denote_eq] at this
  exact this.symm

theorem Expr.of_cancel_le (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.toNormPoly b.toNormPoly = (c.toPoly, d.toPoly)) : (a.denote ctx ≤ b.denote ctx) = (c.denote ctx ≤ d.denote ctx) := by
  have := Poly.denote_le_cancel_eq ctx a.toNormPoly b.toNormPoly
  rw [h] at this
  simp [toNormPoly, Poly.denote_le] at this
  exact this.symm

theorem Expr.of_cancel_lt (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.inc.toNormPoly b.toNormPoly = (c.inc.toPoly, d.toPoly)) : (a.denote ctx < b.denote ctx) = (c.denote ctx < d.denote ctx) :=
  of_cancel_le ctx a.inc b c.inc d h

theorem ExprCnstr.denote_toPoly (ctx : Context) (c : ExprCnstr) : c.toPoly.denote ctx = c.denote ctx := by
  cases c; rename_i eq lhs rhs
  simp [ExprCnstr.denote, PolyCnstr.denote, ExprCnstr.toPoly]
  by_cases h : eq = true <;> simp [h]
  . rw [Poly.denote_eq_cancel_eq]; simp [Poly.denote_eq, Expr.toNormPoly]
  . rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_le, Expr.toNormPoly]

attribute [local simp] ExprCnstr.denote_toPoly

theorem Poly.mul.go_denote (ctx : Context) (k : Nat) (p : Poly) : (Poly.mul.go k p).denote ctx = k * p.denote ctx := by
  match p with
  | [] => rfl
  | (k', v) :: p => simp [Poly.mul.go, go_denote]

attribute [local simp] Poly.mul.go_denote

section
attribute [-simp] Nat.right_distrib Nat.left_distrib

theorem PolyCnstr.denote_mul (ctx : Context) (k : Nat) (c : PolyCnstr) : (c.mul (k+1)).denote ctx = c.denote ctx := by
  cases c; rename_i eq lhs rhs
  have hn : ¬ (k + 1 = 0) := Nat.succ_ne_zero k
  by_cases he : eq = true <;> simp [he, PolyCnstr.mul, PolyCnstr.denote, Poly.denote_le, Poly.denote_eq]
    <;> by_cases hk : k = 0 <;> simp [hk, hn] <;> apply propext <;> apply Iff.intro <;> intro h
  . exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ _) h
  . rw [h]
  . exact Nat.le_of_mul_le_mul_left h (Nat.zero_lt_succ _)
  . apply Nat.mul_le_mul_left _ h

end

attribute [local simp] PolyCnstr.denote_mul

theorem PolyCnstr.denote_combine {ctx : Context} {c₁ c₂ : PolyCnstr} (h₁ : c₁.denote ctx) (h₂ : c₂.denote ctx) : (c₁.combine c₂).denote ctx := by
  cases c₁; cases c₂; rename_i eq₁ lhs₁ rhs₁ eq₂ lhs₂ rhs₂
  simp [denote] at h₁ h₂
  simp [PolyCnstr.combine, denote]
  by_cases he₁ : eq₁ = true <;> by_cases he₂ : eq₂ = true <;> simp [he₁, he₂] at h₁ h₂ |-
  . rw [Poly.denote_eq_cancel_eq]; simp [Poly.denote_eq] at h₁ h₂ |-; simp [h₁, h₂]
  . rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_eq, Poly.denote_le] at h₁ h₂ |-; rw [h₁]; apply Nat.add_le_add_left h₂
  . rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_eq, Poly.denote_le] at h₁ h₂ |-; rw [h₂]; apply Nat.add_le_add_right h₁
  . rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_eq, Poly.denote_le] at h₁ h₂ |-; apply Nat.add_le_add h₁ h₂

attribute [local simp] PolyCnstr.denote_combine

theorem Poly.isNum?_eq_some (ctx : Context) {p : Poly} {k : Nat} : p.isNum? = some k → p.denote ctx = k := by
  simp [isNum?]
  split
  next => intro h; injection h; subst k; simp
  next k v => by_cases h : v = fixedVar <;> simp [h]; intros; simp [Var.denote]; assumption
  next => intros; contradiction

def Poly.of_isZero (ctx : Context) {p : Poly} (h : isZero p = true) : p.denote ctx = 0 := by
  simp [isZero] at h
  simp [h]

def Poly.of_isNonZero (ctx : Context) {p : Poly} (h : isNonZero p = true) : p.denote ctx > 0 := by
  match p with
  | [] => contradiction
  | (k, v) :: p =>
    by_cases he : v = fixedVar <;> simp [he, isNonZero] at h ⊢
    . simp [Var.denote]; apply Nat.lt_of_succ_le; exact Nat.le_trans h (Nat.le_add_right ..)
    . have ih := of_isNonZero ctx h
      exact Nat.le_trans ih (Nat.le_add_right ..)

def PolyCnstr.eq_false_of_isUnsat (ctx : Context) {c : PolyCnstr} : c.isUnsat → c.denote ctx = False := by
  cases c; rename_i eq lhs rhs
  simp [isUnsat]
  by_cases he : eq = true <;> simp [he, denote, Poly.denote_eq, Poly.denote_le]
  . intro
      | Or.inl ⟨h₁, h₂⟩ => simp [Poly.of_isZero, h₁]; have := Nat.not_eq_zero_of_lt (Poly.of_isNonZero ctx h₂); simp [this.symm]
      | Or.inr ⟨h₁, h₂⟩ => simp [Poly.of_isZero, h₂]; have := Nat.not_eq_zero_of_lt (Poly.of_isNonZero ctx h₁); simp [this]
  . intro ⟨h₁, h₂⟩
    simp [Poly.of_isZero, h₂]
    have := Nat.not_le_of_gt (Poly.of_isNonZero ctx h₁)
    simp [this]

def PolyCnstr.eq_true_of_isValid (ctx : Context) {c : PolyCnstr} : c.isValid → c.denote ctx = True := by
  cases c; rename_i eq lhs rhs
  simp [isValid]
  by_cases he : eq = true <;> simp [he, denote, Poly.denote_eq, Poly.denote_le]
  . intro ⟨h₁, h₂⟩
    simp [Poly.of_isZero, h₁, h₂]
  . intro h
    simp [Poly.of_isZero, h]
    have := Nat.zero_le (Poly.denote ctx rhs)
    simp [this]

def ExprCnstr.eq_false_of_isUnsat (ctx : Context) (c : ExprCnstr) (h : c.toPoly.isUnsat) : c.denote ctx = False := by
  have := PolyCnstr.eq_false_of_isUnsat ctx h
  simp at this
  assumption

def ExprCnstr.eq_true_of_isValid (ctx : Context) (c : ExprCnstr) (h : c.toPoly.isValid) : c.denote ctx = True := by
  have := PolyCnstr.eq_true_of_isValid ctx h
  simp at this
  assumption

theorem Certificate.of_combineHyps (ctx : Context) (c : PolyCnstr) (cs : Certificate) (h : (combineHyps c cs).denote ctx → False) : c.denote ctx → cs.denote ctx := by
  match cs with
  | [] => simp [combineHyps, denote] at *; exact h
  | (k, c')::cs =>
    intro h₁ h₂
    have := PolyCnstr.denote_combine (ctx := ctx) (c₂ := PolyCnstr.mul (k + 1) (ExprCnstr.toPoly c')) h₁
    simp at this
    have := this h₂
    have ih := of_combineHyps ctx (PolyCnstr.combine c (PolyCnstr.mul (k + 1) (ExprCnstr.toPoly c'))) cs
    exact ih h this

theorem Certificate.of_combine (ctx : Context) (cs : Certificate) (h : cs.combine.denote ctx → False) : cs.denote ctx := by
  match cs with
  | [] => simp [combine, PolyCnstr.denote, Poly.denote_eq] at h
  | (k, c)::cs =>
    simp [denote, combine] at *
    intro h'
    apply of_combineHyps (h := h)
    simp [h']

theorem Certificate.of_combine_isUnsat (ctx : Context) (cs : Certificate) (h : cs.combine.isUnsat) : cs.denote ctx :=
  have h := PolyCnstr.eq_false_of_isUnsat ctx h
  of_combine ctx cs (fun h' => Eq.mp h h')

example (x₁ x₂ x₃ : Nat) : (x₁ + x₂) + (x₂ + x₃) = x₃ + 2*x₂ + x₁ :=
  Expr.eq_of_toNormPoly { vars := [x₁, x₂, x₃] }
   (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
   (Expr.add (Expr.add (Expr.var 2) (Expr.mulL 2 (Expr.var 1))) (Expr.var 0))
   rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) = x₃ + x₂) = (x₁ + x₂ = 0) :=
  Expr.of_cancel_eq { vars := [x₁, x₂, x₃] }
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) ≤ x₃ + x₂) = (x₁ + x₂ ≤ 0) :=
  Expr.of_cancel_le { vars := [x₁, x₂, x₃] }
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) < x₃ + x₂) = (x₁ + x₂ < 0) :=
  Expr.of_cancel_lt { vars := [x₁, x₂, x₃] }
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x₁ x₂ : Nat) : x₁ + 2 ≤ 3*x₂ → 4*x₂ ≤ 3 + x₁ → 3 ≤ 2*x₂ → False :=
  Certificate.of_combine_isUnsat { vars := [x₁, x₂] }
    [ (1, { eq := false, lhs := Expr.add (Expr.var 0) (Expr.num 2), rhs := Expr.mulL 3 (Expr.var 1) }),
      (1, { eq := false, lhs := Expr.mulL 4 (Expr.var 1), rhs := Expr.add (Expr.num 3) (Expr.var 0) }),
      (0, { eq := false, lhs := Expr.num 3, rhs := Expr.mulL 2 (Expr.var 1) }) ]
    rfl

example (x : Nat) (xs : List Nat) : (sizeOf x < 1 + (1 + sizeOf x + sizeOf xs)) = True :=
  ExprCnstr.eq_true_of_isValid { vars := [sizeOf x, sizeOf xs]  }
    { eq := false, lhs := Expr.inc (Expr.var 0), rhs := Expr.add (Expr.num 1) (Expr.add (Expr.add (Expr.num 1) (Expr.var 0)) (Expr.var 1)) }
    rfl

example (x : Nat) (xs : List Nat) : (1 + (1 + sizeOf x + sizeOf xs) < sizeOf x) = False :=
  ExprCnstr.eq_false_of_isUnsat { vars := [sizeOf x, sizeOf xs]  }
    { eq := false, lhs := Expr.inc <| Expr.add (Expr.num 1) (Expr.add (Expr.add (Expr.num 1) (Expr.var 0)) (Expr.var 1)), rhs := Expr.var 0 }
    rfl
