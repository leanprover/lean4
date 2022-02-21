abbrev Var := Nat

inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mulL (k : Nat) (a : Expr)
  | mulR (a : Expr) (k : Nat)
  deriving Inhabited, Repr

/--
  When encoding polynomials. We use `fixedVar` for encoding numerals.
  The denotation of `fixedVar` is always `1`. -/
def fixedVar := 100000000 -- Any big number should work here

structure Context where
  vars : List Nat

private def List.getIdx : List α → Var → α → α
  | [],    i,   u => u
  | a::as, 0,   u => a
  | a::as, i+1, u => getIdx as i u

def Var.denote (ctx : Context) (v : Var) : Nat :=
  if v = fixedVar then 1 else ctx.vars.getIdx v 0

def Expr.denote (ctx : Context) : Expr → Nat
  | Expr.add a b  => Nat.add (denote ctx a) (denote ctx b)
  | Expr.num k    => k
  | Expr.var v    => v.denote ctx
  | Expr.mulL k e => k * denote ctx e
  | Expr.mulR e k => denote ctx e * k

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.right_distrib Nat.left_distrib Nat.mul_assoc Nat.mul_comm

abbrev Poly := List (Nat × Var)

def Poly.denote (ctx : Context) (p : Poly) : Nat :=
  match p with
  | [] => 0
  | (k, v) :: p => k * v.denote ctx + denote ctx p

def Poly.insertSorted (k : Nat) (v : Var) (p : Poly) : Poly :=
  match p with
  | [] => [(k, v)]
  | (k', v') :: p => if v < v' then (k, v) :: (k', v') :: p else (k', v') :: insertSorted k v p

@[simp] theorem Poly.denote_insertSorted (ctx : Context) (k : Nat) (v : Var) (p : Poly) : (p.insertSorted k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  match p with
  | [] => simp [insertSorted, denote]
  | (k', v') :: p => by_cases h : v < v' <;> simp [h, insertSorted, denote, denote_insertSorted]

def Poly.sort (p : Poly) : Poly :=
  let rec go (p : Poly) (r : Poly) : Poly :=
    match p with
    | [] => r
    | (k, v) :: p => go p (r.insertSorted k v)
  go p []

@[simp] theorem Poly.denote_sort_go (ctx : Context) (p : Poly) (r : Poly) : (sort.go p r).denote ctx = p.denote ctx + r.denote ctx := by
  match p with
  | [] => simp [sort.go, denote]
  | (k, v):: p => simp [sort.go, denote, denote_sort_go]

@[simp] theorem Poly.denote_sort (ctx : Context) (m : Poly) : m.sort.denote ctx = m.denote ctx := by
  simp [sort, denote]

@[simp] theorem Poly.denote_append (ctx : Context) (p q : Poly) : (p ++ q).denote ctx = p.denote ctx + q.denote ctx := by
  match p with
  | []  => simp [denote]
  | (k, v) :: p => simp [denote, denote_append]

@[simp] theorem Poly.denote_cons (ctx : Context) (k : Nat) (v : Var) (p : Poly) : denote ctx ((k, v) :: p) = k * v.denote ctx + p.denote ctx := by
  match p with
  | []     => simp [denote]
  | _ :: m => simp [denote, denote_cons]

@[simp] theorem Poly.denote_reverseAux (ctx : Context) (p q : Poly) : denote ctx (List.reverseAux p q) = denote ctx (p ++ q) := by
  match p with
  | [] => simp [denote, List.reverseAux]
  | (k, v) :: p => simp [denote, List.reverseAux, denote_reverseAux]

@[simp] theorem Poly.denote_reverse (ctx : Context) (p : Poly) : denote ctx (List.reverse p) = denote ctx p := by
  simp [List.reverse]

def Poly.fuse (p : Poly) : Poly :=
  match p with
  | []  => []
  | (k, v) :: p =>
    match fuse p with
    | [] => [(k, v)]
    | (k', v') :: p' => if v = v' then (k+k', v)::p' else (k, v) :: (k', v') :: p'

@[simp] theorem Poly.denote_fuse (ctx : Context) (p : Poly) : p.fuse.denote ctx = p.denote ctx := by
  match p with
  | [] => rfl
  | (k, v) :: p =>
    have ih := denote_fuse ctx p
    simp [fuse, denote]
    split
    case _ h => simp [denote, ← ih, h]
    case _ k' v' p' h => by_cases he : v = v' <;> simp [he, denote, ← ih, h]

def Poly.mul (k : Nat) (p : Poly) : Poly :=
  if k = 0 then
    []
  else
    go p
where
  go : Poly → Poly
  | [] => []
  | (k', v) :: p => (k*k', v) :: go p

@[simp] theorem Poly.denote_mul (ctx : Context) (k : Nat) (p : Poly) : (p.mul k).denote ctx = k * p.denote ctx := by
  simp [mul]
  by_cases h : k = 0
  . simp [denote, h]
  . simp [denote, h]
    induction p with
    | nil  => simp [mul.go, denote]
    | cons kv m ih => cases kv with | _ k' v => simp [mul.go, denote, ih]

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

def Poly.denote_eq (ctx : Context) (mp : Poly × Poly) : Prop := mp.1.denote ctx = mp.2.denote ctx

theorem Poly.denote_eq_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂)) : denote_eq ctx (cancelAux fuel m₁ m₂ r₁ r₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp [cancelAux]
    split <;> simp at h <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv]
    . apply ih; simp [denote_eq, denote] at h |-; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv]
      . apply ih; simp [denote_eq, denote] at h |-; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk]
        . apply ih
          simp [denote_eq, denote] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Eq.symm
          apply Nat.sub_eq_of_eq_add
          simp [h]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk]
          . apply ih
            simp [denote_eq, denote] at h |-
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
            apply Nat.sub_eq_of_eq_add
            simp [h]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            apply ih
            simp [denote_eq, denote] at h |-
            rw [← Nat.add_assoc, ← Nat.add_assoc] at h
            exact Nat.add_right_cancel h

theorem Poly.of_denote_eq_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_eq ctx (cancelAux fuel m₁ m₂ r₁ r₂)) : denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp [cancelAux] at h
    split at h <;> simp <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv] at h
    . have ih := ih (h := h); simp [denote_eq, denote] at ih ⊢; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv] at h
      . have ih := ih (h := h); simp [denote_eq, denote] at ih ⊢; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk] at h
        . have ih := ih (h := h); simp [denote_eq, denote] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih.symm
          simp at ih
          rw [ih]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk] at h
          . have ih := ih (h := h); simp [denote_eq, denote] at ih ⊢
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
            have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih
            simp at ih
            rw [ih]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            have ih := ih (h := h); simp [denote_eq, denote] at ih ⊢
            rw [← Nat.add_assoc, ih, Nat.add_assoc]

def Poly.cancel (m₁ m₂ : Poly) : Poly × Poly :=
  cancelAux (m₁.length + m₂.length) m₁ m₂ [] []

theorem Poly.denote_eq_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_eq ctx (m₁, m₂)) : denote_eq ctx (cancel m₁ m₂) := by
  simp [cancel]; apply denote_eq_cancelAux; simp [h]

theorem Poly.of_denote_eq_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_eq ctx (cancel m₁ m₂)) : denote_eq ctx (m₁, m₂) := by
  simp [cancel] at h
  have := Poly.of_denote_eq_cancelAux (h := h)
  simp at this
  assumption

theorem Poly.denote_eq_cancel_eq (ctx : Context) (m₁ m₂ : Poly) : denote_eq ctx (cancel m₁ m₂) = denote_eq ctx (m₁, m₂) :=
  propext <| Iff.intro (fun h => of_denote_eq_cancel h) (fun h => denote_eq_cancel h)

def Poly.denote_le (ctx : Context) (mp : Poly × Poly) : Prop := mp.1.denote ctx ≤ mp.2.denote ctx

theorem Poly.denote_le_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_le ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂)) : denote_le ctx (cancelAux fuel m₁ m₂ r₁ r₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp [cancelAux]
    split <;> simp at h <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv]
    . apply ih; simp [denote_le, denote] at h |-; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv]
      . apply ih; simp [denote_le, denote] at h |-; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk]
        . apply ih
          simp [denote_le, denote] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Nat.le_sub_of_add_le
          simp [h]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk]
          . apply ih
            simp [denote_le, denote] at h |-
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
            apply Nat.sub_le_of_le_add (Nat.le_trans haux (Nat.le_add_left ..))
            simp [h]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            apply ih
            simp [denote_le, denote] at h |-
            rw [← Nat.add_assoc, ← Nat.add_assoc] at h
            apply Nat.le_of_add_le_add_right h
    done

theorem Poly.of_denote_le_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_le ctx (cancelAux fuel m₁ m₂ r₁ r₂)) : denote_le ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp [cancelAux] at h
    split at h <;> simp <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv] at h
    . have ih := ih (h := h); simp [denote_le, denote] at ih ⊢; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv] at h
      . have ih := ih (h := h); simp [denote_le, denote] at ih ⊢; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk] at h
        . have ih := ih (h := h); simp [denote_le, denote] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have := Nat.add_le_of_le_sub (Nat.le_trans haux (Nat.le_add_left ..)) ih
          simp at this
          exact this
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk] at h
          . have ih := ih (h := h); simp [denote_le, denote] at ih ⊢
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
            have := Nat.le_add_of_sub_le (Nat.le_trans haux (Nat.le_add_left ..)) ih
            simp at this
            exact this
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            have ih := ih (h := h); simp [denote_le, denote] at ih ⊢
            have := Nat.add_le_add_right ih (k₁ * Var.denote ctx v₁)
            simp at this
            exact this

theorem Poly.denote_le_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_le ctx (m₁, m₂)) : denote_le ctx (cancel m₁ m₂) := by
  simp [cancel]; apply denote_le_cancelAux; simp [h]

theorem Poly.of_denote_le_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_le ctx (cancel m₁ m₂)) : denote_le ctx (m₁, m₂) := by
  simp [cancel] at h
  have := Poly.of_denote_le_cancelAux (h := h)
  simp at this
  assumption

theorem Poly.denote_le_cancel_eq (ctx : Context) (m₁ m₂ : Poly) : denote_le ctx (cancel m₁ m₂) = denote_le ctx (m₁, m₂) :=
  propext <| Iff.intro (fun h => of_denote_le_cancel h) (fun h => denote_le_cancel h)

def Expr.toPoly : Expr → Poly
  | Expr.num k    => if k = 0 then [] else [ (k, fixedVar) ]
  | Expr.var i    => [(1, i)]
  | Expr.add a b  => a.toPoly ++ b.toPoly
  | Expr.mulL k a => a.toPoly.mul k
  | Expr.mulR a k => a.toPoly.mul k

@[simp] theorem Expr.denote_toPoly (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k => by_cases h : k = 0 <;> simp [toPoly, h, Poly.denote, Var.denote, denote]
  | var i => simp [denote, toPoly, Poly.denote, Poly.denote]
  | add a b iha ihb => simp [denote, toPoly, iha, ihb]; done
  | mulL k a ih => simp [denote, toPoly, ih]; done
  | mulR k a ih => simp [denote, toPoly, ih]; done

def Expr.toNormPoly (e : Expr) : Poly :=
  e.toPoly.sort.fuse

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

def Expr.inc (e : Expr) : Expr :=
   Expr.add e (Expr.num 1)

theorem Expr.of_cancel_lt (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.inc.toNormPoly b.toNormPoly = (c.inc.toPoly, d.toPoly)) : (a.denote ctx < b.denote ctx) = (c.denote ctx < d.denote ctx) :=
  of_cancel_le ctx a.inc b c.inc d h

structure ExprLe where
  lhs : Expr
  rhs : Expr
  deriving Repr

def ExprLe.denote (ctx : Context) (c : ExprLe) := c.lhs.denote ctx ≤ c.rhs.denote ctx

def ExprLe.add (c d : ExprLe) : ExprLe :=
  { lhs := Expr.add c.lhs d.lhs, rhs := Expr.add c.rhs d.rhs }

def ExprLe.toNormPoly (c : ExprLe) : Poly × Poly :=
  Poly.cancel c.lhs.toNormPoly c.rhs.toNormPoly

def ExprLe.toPoly (c : ExprLe) : Poly × Poly :=
  (c.lhs.toPoly, c.rhs.toPoly)

theorem ExprLe.combine (ctx : Context) (c d e : ExprLe) (h₁ : c.denote ctx) (h₂ : d.denote ctx) (h₃ : e.toPoly = (c.add d).toNormPoly) : e.denote ctx := by
  match c, d, e with
  | { lhs := cLhs, rhs := cRhs }, { lhs := dLhs, rhs := dRhs }, { lhs := eLhs, rhs := eRhs } =>
    simp [add, denote, Expr.denote, toPoly, toNormPoly] at h₁ h₂ h₃ |-
    rw [← Expr.of_cancel_le ctx (h := h₃.symm)]
    exact Nat.add_le_add h₁ h₂

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

example (x₁ x₂) (h₁ : x₁ + 2 ≤ 3*x₂) (h₂ : 4*x₂ ≤ 3 + x₁) : x₂ ≤ 1 :=
  ExprLe.combine { vars := [x₁, x₂] }
    { lhs := Expr.add (Expr.var 0) (Expr.num 2), rhs := Expr.mulL 3 (Expr.var 1) }
    { lhs := Expr.mulL 4 (Expr.var 1), rhs := Expr.add (Expr.num 3) (Expr.var 0) }
    { lhs := Expr.var 1, rhs := Expr.num 1 }
    h₁
    h₂
    rfl
