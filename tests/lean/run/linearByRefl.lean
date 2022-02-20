abbrev Var := Nat

inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mulL (k : Nat) (a : Expr)
  | mulR (a : Expr) (k : Nat)
  deriving Inhabited, Repr

structure Context where
  vars : List Nat

def List.getIdx : List α → Var → α → α
  | [],    i,   u => u
  | a::as, 0,   u => a
  | a::as, i+1, u => getIdx as i u

def Var.denote (ctx : Context) (v : Var) : Nat :=
  ctx.vars.getIdx v 0

def Expr.denote (ctx : Context) : Expr → Nat
  | Expr.add a b  => Nat.add (denote ctx a) (denote ctx b)
  | Expr.num k    => k
  | Expr.var v    => v.denote ctx
  | Expr.mulL k e => k * denote ctx e
  | Expr.mulR e k => denote ctx e * k

abbrev Monomials := List (Nat × Var)

def Monomials.denote (ctx : Context) (m : Monomials) : Nat :=
  match m with
  | [] => 0
  | (k, v) :: m => k * v.denote ctx + denote ctx m

def Monomials.addM (m : Monomials) (k : Nat) (v : Var) : Monomials :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: m => if v = v' then (k' + k, v) :: m else (k', v') :: addM m k v

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.right_distrib Nat.left_distrib Nat.mul_assoc Nat.mul_comm

@[simp] theorem Monomials.denote_addM (ctx : Context) (m : Monomials) (k : Nat) (v : Var) : (m.addM k v).denote ctx = m.denote ctx + k * v.denote ctx := by
  induction m with
  | nil => simp [denote]
  | cons kv m ih => cases kv with | _ k' v' =>
    by_cases h : v = v'
    . simp [h, denote, addM]
    . simp [h, denote, addM, ih]

def Monomials.add (m₁ m₂ : Monomials) : Monomials :=
  match m₂ with
  | [] => m₁
  | (k, v) :: m₂ => add (m₁.addM k v) m₂

@[simp] theorem Monomials.denote_add (ctx : Context) (m₁ m₂ : Monomials) : (m₁.add m₂).denote ctx = m₁.denote ctx + m₂.denote ctx := by
  induction m₂ generalizing m₁ with
  | nil => simp [add, denote]
  | cons kv m₂ ih => cases kv with | _ k v =>
    simp [add, denote, ih]

def Monomials.mul (k : Nat) (m : Monomials) : Monomials :=
  if k = 0 then
    []
  else
    go m
where
  go : Monomials → Monomials
  | [] => []
  | (k', v) :: m => (k*k', v) :: go m

@[simp] theorem Monomials.denote_mul (ctx : Context) (k : Nat) (m : Monomials) : (m.mul k).denote ctx = k * m.denote ctx := by
  simp [mul]
  by_cases h : k = 0
  . simp [denote, h]
  . simp [denote, h]
    induction m with
    | nil  => simp [mul.go, denote]
    | cons kv m ih => cases kv with | _ k' v => simp [mul.go, denote, ih]

def Monomials.insertSorted (k : Nat) (v : Var) (m : Monomials) : Monomials :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: m => if v < v' then (k, v) :: (k', v') :: m else (k', v') :: insertSorted k v m

@[simp] theorem Monomials.denote_insertSorted (ctx : Context) (k : Nat) (v : Var) (m : Monomials) : (m.insertSorted k v).denote ctx = m.denote ctx + k * v.denote ctx := by
  induction m with
  | nil => simp [insertSorted, denote]
  | cons kv m ih => cases kv with | _ k' v' => by_cases h : v < v' <;> simp [h, insertSorted, denote, ih]

def Monomials.sort (m : Monomials) : Monomials :=
  let rec go (m : Monomials) (r : Monomials) : Monomials :=
    match m with
    | [] => r
    | (k, v) :: m => go m (r.insertSorted k v)
  go m []

@[simp] theorem Monomials.denote_sort_go (ctx : Context) (m : Monomials) (r : Monomials) : (sort.go m r).denote ctx = m.denote ctx + r.denote ctx := by
  induction m generalizing r with
  | nil => simp [sort.go, denote]; done
  | cons kv m ih => cases kv with | _ k v => simp [sort.go, denote, ih]

@[simp] theorem Monomials.denote_sort (ctx : Context) (m : Monomials) : m.sort.denote ctx = m.denote ctx := by
  simp [sort, denote]

@[simp] theorem Monomials.denote_append (ctx : Context) (m₁ m₂ : Monomials) : (m₁ ++ m₂).denote ctx = m₁.denote ctx + m₂.denote ctx := by
  match m₁ with
  | []  => simp [denote]
  | (k, v) :: m₁ => simp [denote, denote_append ctx m₁ m₂]

@[simp] theorem Monomials.denote_cons (ctx : Context) (k : Nat) (v : Var) (m : Monomials) : denote ctx ((k, v) :: m) = k * v.denote ctx + m.denote ctx := by
  match m with
  | []  => simp [denote]
  | _ :: m => simp [denote, denote_cons ctx k v m]

@[simp] theorem Monomials.denote_reverseAux (ctx : Context) (m₁ m₂ : Monomials) : denote ctx (List.reverseAux m₁ m₂) = denote ctx (m₁ ++ m₂) := by
  match m₁ with
  | [] => simp [denote, List.reverseAux]
  | (k, v) :: m₁ => simp [denote, List.reverseAux, denote_reverseAux ctx m₁]

@[simp] theorem Monomials.denote_reverse (ctx : Context) (m : Monomials) : denote ctx (List.reverse m) = denote ctx m := by
  simp [List.reverse]

def Monomials.cancelAux (fuel : Nat) (m₁ m₂ r₁ r₂ : Monomials) : Monomials × Monomials :=
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

def Monomials.denote_eq (ctx : Context) (mp : Monomials × Monomials) : Prop := mp.1.denote ctx = mp.2.denote ctx

-- TODO : cleanup proof
theorem Monomials.denote_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Monomials)
    (h : denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂)) : denote_eq ctx (cancelAux fuel m₁ m₂ r₁ r₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp [cancelAux]
    split
    . simp_all
    . simp_all
    . rename_i k₁ v₁ m₁ k₂ v₂ m₂
      by_cases hltv : v₁ < v₂
      . simp [hltv]; apply ih; simp [denote_eq, denote] at h |-; assumption
      . by_cases hgtv : v₁ > v₂
        . simp [hltv, hgtv]; apply ih; simp [denote_eq, denote] at h |-; assumption
        . simp [hltv, hgtv]
          have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv)
          subst heqv
          by_cases hltk : k₁ < k₂
          . simp [hltk]; apply ih; simp [denote_eq, denote] at h |-
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc]
            apply Eq.symm
            apply Nat.sub_eq_of_eq_add
            simp [h]
            exact Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          . by_cases hgtk : k₁ > k₂
            . simp [hltk, hgtk]
              apply ih
              simp [denote_eq, denote] at h |-
              rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc]
              apply Nat.sub_eq_of_eq_add
              simp [h]
              exact Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            . simp [hltk, hgtk]
              have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk)
              subst heqk
              apply ih
              simp [denote_eq, denote] at h |-
              rw [← Nat.add_assoc, ← Nat.add_assoc] at h
              exact Nat.add_right_cancel h

def Monomials.cancel (m₁ m₂ : Monomials) : Monomials × Monomials :=
  cancelAux (m₁.length + m₂.length) m₁ m₂ [] []

theorem Monomials.denote_cancel (ctx : Context) (m₁ m₂ : Monomials) (h : denote_eq ctx (m₁, m₂)) : denote_eq ctx (cancel m₁ m₂) := by
  simp [cancel]
  apply denote_cancelAux
  simp [h]

structure Poly where
  m : Monomials := []
  k : Nat       := 0
  deriving Repr

def Poly.denote (ctx : Context) (p : Poly) : Nat :=
  p.m.denote ctx + p.k

def Poly.addK (p : Poly) (k : Nat) : Poly :=
  { p with k := p.k + k }

def Poly.addM (p : Poly) (k : Nat) (v : Var) : Poly :=
  { p with m := p.m.addM k v }

@[simp] theorem Poly.denote_addM (ctx : Context) (p : Poly) (k : Nat) (v : Var) : (p.addM k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  simp [denote, addM]

def Poly.add (p q : Poly) : Poly :=
  { m := p.m.add q.m, k := p.k + q.k }

@[simp] theorem Poly.denote_add (ctx : Context) (p q : Poly) : (p.add q).denote ctx = p.denote ctx + q.denote ctx := by
  simp [add, denote]

def Poly.mul (k : Nat) (p : Poly) : Poly :=
  { p with m := p.m.mul k, k := p.k * k }

@[simp] theorem Poly.denote_mul (ctx : Context) (k : Nat) (p : Poly) : (p.mul k).denote ctx = k * p.denote ctx := by
  simp [denote, mul]

def Poly.sort (p : Poly) : Poly :=
  { p with m := p.m.sort }

@[simp] theorem Poly.denote_sort (ctx : Context) (p : Poly) : p.sort.denote ctx = p.denote ctx := by
  simp [denote, sort]

def Expr.toPoly : Expr → Poly
  | Expr.num k    => { k }
  | Expr.var i    => { m := [(1, i)] }
  | Expr.add a b  => a.toPoly.add b.toPoly
  | Expr.mulL k a => a.toPoly.mul k
  | Expr.mulR a k => a.toPoly.mul k

@[simp] theorem Expr.denote_toPoly (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k => simp [denote, toPoly, Poly.denote, Monomials.denote]
  | var i => simp [denote, toPoly, Poly.denote, Monomials.denote]
  | add a b iha ihb => simp [denote, toPoly, iha, ihb]; done
  | mulL k a ih => simp [denote, toPoly, ih]; done
  | mulR k a ih => simp [denote, toPoly, ih]; done

theorem Expr.eq_of_toPoly_sort_eq (ctx : Context) (a b : Expr) (h : a.toPoly.sort = b.toPoly.sort) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) h
  simp at h
  assumption

example (x₁ x₂ x₃ : Nat) : (x₁ + x₂) + (x₂ + x₃) = x₃ + 2*x₂ + x₁ :=
  Expr.eq_of_toPoly_sort_eq { vars := [x₁, x₂, x₃] }
   (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
   (Expr.add (Expr.add (Expr.var 2) (Expr.mulL 2 (Expr.var 1))) (Expr.var 0))
   rfl
