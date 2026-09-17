module
public import Lean.Level
import all Lean.Level
import all Lean.Data.Name
public import Std.Data.TreeSet.Basic
public import Std.Data.ExtTreeSet.Basic
public import Std.Data.ExtTreeSet.Lemmas
public import Init.Data.Ord.String

namespace Lean.Level

@[simp, grind =]
def SortedAssocList.toList {cmp : α → α → Ordering} :
    SortedAssocList α β cmp → List (α × β)
  | .nil => []
  | .cons k v t => (k, v) :: t.toList

theorem SortedAssocList.toList_inj {cmp : α → α → Ordering}
    {x y : SortedAssocList α β cmp} : x.toList = y.toList ↔ x = y := by
  induction x generalizing y <;> cases y <;> simp_all [and_assoc]

attribute [simp] SortedSetNode.toList
attribute [simp] SortedSet.toList?.eq_1 SortedSet.toList?.eq_2 SortedSet.toList?.eq_3

structure CompareOrder (α : Type u) (cmp : α → α → Ordering) where
  mk (cmp) ::
  value : α
deriving DecidableEq

instance : LE (CompareOrder α cmp) where
  le a b := (cmp a.value b.value).isLE

instance : LT (CompareOrder α cmp) where
  lt a b := cmp a.value b.value = .lt

instance : DecidableLE (CompareOrder α cmp) := fun _ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidableLT (CompareOrder α cmp) := fun _ _ => inferInstanceAs (Decidable (_ = _))

theorem CompareOrder.le_def {a b : CompareOrder α cmp} :
    a ≤ b ↔ (cmp a.value b.value).isLE := Iff.rfl

theorem CompareOrder.lt_def {a b : CompareOrder α cmp} :
    a < b ↔ cmp a.value b.value = .lt := Iff.rfl

theorem Ordering.isLE_or_isGE_eq : ∀ {o : Ordering}, (o.isLE || o.isGE) = true := by decide

instance {cmp} [Std.TransCmp cmp] : Std.IsLinearPreorder (CompareOrder α cmp) where
  le_refl := by simp [CompareOrder.le_def, Std.ReflCmp.compare_self]
  le_trans _ _ _ := Std.TransCmp.isLE_trans
  le_total a b := by
    rw [CompareOrder.le_def, CompareOrder.le_def,
      ← Std.OrientedCmp.isGE_iff_isLE, or_comm, ← Bool.or_eq_true,
      Ordering.isLE_or_isGE_eq]

instance {cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    Std.IsLinearOrder (CompareOrder α cmp) where
  le_antisymm a b h h' := by
    rw [CompareOrder.le_def] at *
    rw [← Std.OrientedCmp.isGE_iff_isLE] at h'
    have := Bool.and_eq_true_iff.mpr ⟨h, h'⟩
    simp [Ordering.isLE_and_isGE_eq] at this
    exact congrArg (CompareOrder.mk cmp) this

instance {cmp} [Std.OrientedCmp cmp] :
    Std.LawfulOrderLT (CompareOrder α cmp) where
  lt_iff a b := by
    simp +contextual [CompareOrder.lt_def, CompareOrder.le_def,
      Std.OrientedCmp.gt_iff_lt (a := b.value)]

@[grind inj]
theorem CompareOrder.value_inj : Function.Injective (CompareOrder.value (cmp := cmp)) := by
  intro a b h
  exact congrArg (CompareOrder.mk cmp) h

theorem CompareOrder.cmp_eq (cmp : α → α → Ordering) [Std.OrientedCmp cmp] (a b : α) :
    cmp a b =
      if CompareOrder.mk cmp a ≤ CompareOrder.mk cmp b then
        if CompareOrder.mk cmp b ≤ CompareOrder.mk cmp a then
          .eq
        else .lt
      else .gt := by
  simp only [CompareOrder.le_def, ← Std.OrientedCmp.isGE_iff_isLE (a := a)]
  generalize cmp a b = o
  decide +revert


structure SortedSetNode.WF (x : SortedSetNode α cmp) : Prop where
  pairwise : List.Pairwise (fun a b => cmp a b = .lt) x.toList

structure SortedSet.WF (x : SortedSet α cmp) : Prop where
  pairwise : ∀ a, x.toList? = some a → List.Pairwise (fun a b => cmp a b = .lt) a

@[simp, grind .]
theorem SortedSet.wf_nil : (nil : SortedSet α cmp).WF := by constructor; simp [toList?]

@[simp, grind .]
theorem SortedSetNode.wf_nil : (nil : SortedSetNode α cmp).WF := by constructor; simp [toList]

@[simp, grind .]
theorem SortedSet.wf_never : (never : SortedSet α cmp).WF := by constructor; simp [toList?]

@[simp, grind =]
theorem SortedSet.wf_cons_iff {k : α} {t : SortedSetNode α cmp} :
    (cons k t).WF ↔ (∀ k' ∈ t.toList, cmp k k' = .lt) ∧ t.WF := by
  constructor
  · intro ⟨h⟩
    simp only [toList?, Option.some.injEq, forall_eq', List.pairwise_cons] at h
    exact ⟨h.1, ⟨h.2⟩⟩
  · intro ⟨h, ⟨h'⟩⟩
    constructor
    simpa using And.intro h h'

@[simp, grind =]
theorem SortedSetNode.wf_cons_iff {k : α} {t : SortedSetNode α cmp} :
    (cons k t).WF ↔ (∀ k' ∈ t.toList, cmp k k' = .lt) ∧ t.WF := by
  constructor
  · intro ⟨h⟩
    simp only [toList, List.pairwise_cons] at h
    exact ⟨h.1, ⟨h.2⟩⟩
  · intro ⟨h, ⟨h'⟩⟩
    constructor
    simpa using And.intro h h'

@[grind =, simp]
theorem SortedSetNode.mem_insert {α : Type} {cmp}
    [Std.LawfulEqCmp cmp] {x : SortedSetNode α cmp} (h : x.WF) {k k' : α} :
    k' ∈ (x.insert k).toList ↔ k' ∈ x.toList ∨ k' = k := by
  fun_induction insert with simp_all <;> grind

@[grind =, simp]
theorem SortedSetNode.mem_merge {α : Type} {cmp}
    [Std.LawfulEqCmp cmp] {x y : SortedSetNode α cmp} (hx : x.WF) (hy : y.WF) {k : α} :
    k ∈ (x.merge y).toList ↔ k ∈ x.toList ∨ k ∈ y.toList := by
  fun_induction merge with simp_all <;> grind

@[grind =, simp]
theorem SortedSetNode.contains_iff_mem {α : Type} {cmp}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {x : SortedSetNode α cmp} (h : x.WF) {k : α} :
    x.contains k ↔ k ∈ x.toList := by
  fun_induction contains with simp_all <;> grind [CompareOrder.cmp_eq (cmp := cmp)]

@[grind .]
theorem SortedSetNode.WF.insert {α : Type} {cmp}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x : SortedSetNode α cmp} (h : x.WF) (k : α) :
    (x.insert k).WF := by
  fun_induction insert with simp_all [or_imp] <;>
    grind [→ Std.TransCmp.lt_trans (cmp := cmp), Std.OrientedCmp.gt_iff_lt (cmp := cmp)]

@[grind .]
theorem SortedSet.WF.insert {α : Type} {cmp}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {x : SortedSet α cmp}
    (h : x.WF) (k : α) : (x.insert k).WF := by
  fun_cases insert with simp_all [or_imp] <;>
    grind [→ Std.TransCmp.lt_trans (cmp := cmp), Std.OrientedCmp.gt_iff_lt (cmp := cmp)]

@[grind .]
theorem SortedSetNode.WF.merge {α : Type} {cmp}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x y : SortedSetNode α cmp} (hx : x.WF) (hy : y.WF) :
    (x.merge y).WF := by
  fun_induction merge with simp_all [or_imp] <;> grind [CompareOrder.cmp_eq (cmp := cmp)]

@[grind .]
theorem SortedSet.WF.merge {α : Type} {cmp}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x y : SortedSet α cmp} (hx : x.WF) (hy : y.WF) :
    (x.merge y).WF := by
  fun_cases merge with simp_all [or_imp] <;> grind [CompareOrder.cmp_eq (cmp := cmp)]

@[grind =, simp]
theorem SortedSetNode.mem_erase {α : Type} {cmp}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {x : SortedSetNode α cmp}
    (h : x.WF) {k k' : α} :
    k' ∈ (x.erase k).toList ↔ k' ∈ x.toList ∧ ¬ k' = k := by
  fun_induction erase with simp_all [or_imp] <;>
    grind [→ Std.TransCmp.lt_trans (cmp := cmp)]

@[grind .]
theorem SortedSetNode.WF.erase {α : Type} {cmp}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x : SortedSetNode α cmp} (h : x.WF) (k : α) :
    (x.erase k).WF := by fun_induction erase with simp_all

structure SortedAssocList.WF (x : SortedAssocList α β cmp) : Prop where
  pairwise : List.Pairwise (fun a b => cmp a.1 b.1 = .lt) x.toList

@[simp, grind .]
theorem SortedAssocList.wf_nil : (nil : SortedAssocList α β cmp).WF := by
  constructor; simp [toList]

@[simp, grind =]
theorem SortedAssocList.wf_cons_iff {k : α} {v : β} {t : SortedAssocList α β cmp} :
    (cons k v t).WF ↔ (∀ k' ∈ t.toList, cmp k k'.1 = .lt) ∧ t.WF := by
  constructor
  · intro ⟨h⟩
    simp only [toList, List.pairwise_cons] at h
    exact ⟨h.1, ⟨h.2⟩⟩
  · intro ⟨h, ⟨h'⟩⟩
    constructor
    simpa using And.intro h h'

@[grind =_]
theorem SortedAssocList.find?_eq_some_iff {α : Type} {cmp} [Max β]
    [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
    {x : SortedAssocList α β cmp} (h : x.WF) {k : α} {v : β} :
    x.find? k = some v ↔ (k, v) ∈ x.toList := by
  fun_induction find? with simp_all <;> grind [= CompareOrder.cmp_eq (cmp := cmp)]

@[grind =, simp]
theorem SortedAssocList.mem_erase {α : Type} {cmp}
    [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
    {x : SortedAssocList α β cmp} (h : x.WF) {k k' : α} {v' : β} :
    (k', v') ∈ (x.erase k).toList ↔ (k', v') ∈ x.toList ∧ ¬ k' = k := by
  fun_induction erase with simp_all <;> grind [= CompareOrder.cmp_eq (cmp := cmp)]

@[grind =]
theorem SortedAssocList.find?_insertMax {α : Type} {cmp} [Max β]
    [Std.LawfulEqCmp cmp] [DecidableEq α] [Std.TransCmp cmp]
    {x : SortedAssocList α β cmp} (h : x.WF) {k k' : α} {v : β} :
    (x.insertMax k v).find? k' =
      match x.find? k' with
      | none => if k = k' then some v else none
      | some v' => if k = k' then Max.max v v' else v' := by
  fun_induction insertMax with simp_all [find?] <;> grind [CompareOrder.cmp_eq (cmp := cmp)]

@[grind =, simp]
theorem SortedAssocList.find?_merge {α : Type} {cmp} [Max β]
    [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
    {x y : SortedAssocList α β cmp} (hx : x.WF) (hy : y.WF) {k : α} :
    (x.merge y).find? k = Max.max (x.find? k) (y.find? k) := by
  fun_induction merge with simp_all [find?] <;> grind [CompareOrder.cmp_eq (cmp := cmp)]

theorem SortedAssocList.ext {α : Type} {cmp} [Max β]
    [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
    {x y : SortedAssocList α β cmp} (hx : x.WF) (hy : y.WF) (h : ∀ k, x.find? k = y.find? k) :
    x = y := by
  simp +singlePass only [Option.ext_iff] at h
  simp only [find?_eq_some_iff, hx, hy] at h
  induction x generalizing y <;> cases y
  case nil.nil => rfl
  case nil.cons k v t => grind
  case cons.nil k v t _ => grind
  case cons.cons k v t ih k' v' t' =>
    cases hk : cmp k k' <;> grind [CompareOrder.cmp_eq (cmp := cmp)]

@[grind .]
theorem SortedAssocList.WF.insertMax {α : Type} {cmp} [Max β]
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x : SortedAssocList α β cmp} (h : x.WF) (k : α) (v : β) :
    (x.insertMax k v).WF := by
  classical
  fun_induction insertMax with simp_all +contextual [-Prod.forall]
  | case2 => grind [CompareOrder.cmp_eq (cmp := cmp)]
  | case4 k' v' t hk ih =>
    intro (k2, v2)
    simp [← SortedAssocList.find?_eq_some_iff, find?_insertMax, *]
    split
    · grind [CompareOrder.cmp_eq (cmp := cmp)]
    · simp_all [SortedAssocList.find?_eq_some_iff]
      grind [CompareOrder.cmp_eq (cmp := cmp)]

@[grind .]
theorem SortedAssocList.WF.erase {α : Type} {cmp}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x : SortedAssocList α β cmp} (h : x.WF) (k : α) :
    (x.erase k).WF := by
  fun_induction erase with simp_all <;> grind [CompareOrder.cmp_eq (cmp := cmp)]

@[grind .]
theorem SortedAssocList.WF.merge {α : Type} {cmp} [Max β]
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x y : SortedAssocList α β cmp} (hx : x.WF) (hy : y.WF) :
    (x.merge y).WF := by
  fun_induction merge with (try simp_all +contextual [-Prod.forall]; done)
  | case3 | case4 | case5 =>
    have hx' := by simpa using hx
    have hy' := by simpa using hy
    rw [wf_cons_iff]
    simp_all only [and_true, true_implies]
    intro (a, b) h
    rw [← find?_eq_some_iff ‹_›, find?_merge (by simp [*]) (by simp [*]), Option.max_eq_some_iff] at h
    simp [find?_eq_some_iff, *] at h
    grind [CompareOrder.cmp_eq (cmp := cmp)]

instance : Std.LawfulOrderOrd String where
  isLE_compare _ _ := isLE_compareOfLessAndEq String.le_antisymm String.not_le String.le_total
  isGE_compare _ _ := isGE_compareOfLessAndEq String.le_antisymm String.not_le String.le_total

instance : Std.TransCmp Name.quickCmpAux where
  eq_swap {a b} := by
    induction a generalizing b <;> cases b <;> simp_all [Name.quickCmpAux] <;>
      split <;> split <;> simp_all [← Std.OrientedOrd.eq_swap]
  isLE_trans {a b c} h h' := by
    induction a generalizing b c <;> cases b <;> simp_all [Name.quickCmpAux] <;>
      cases c <;> simp_all [Name.quickCmpAux] <;> split at h <;> split at h' <;>
      split <;> simp_all [Std.LawfulOrderOrd.isLE_compare] <;> grind

instance : Std.LawfulEqCmp Name.quickCmpAux where
  eq_of_compare {a b} h := by fun_induction Name.quickCmpAux with simp_all

instance : Std.TransCmp Name.quickCmp where
  eq_swap {a b} := by
    simp [Name.quickCmp] <;> split <;> split <;> simp [← Std.OrientedCmp.eq_swap] <;> grind
  isLE_trans {a b c} h h' := by
    simp [Name.quickCmp] at * <;> split at h <;> split at h' <;> split <;>
      simp_all [Std.LawfulOrderOrd.isLE_compare] <;>
      grind [Std.TransCmp.isLE_trans (cmp := Name.quickCmpAux)]

instance : Std.LawfulEqCmp Name.quickCmp where
  eq_of_compare {a b} h := by rw [Name.quickCmp] at h; split at h <;> simp_all

def SortedSet.All (p : α → Prop) (set : SortedSet α cmp) : Prop :=
  ∃ a, set.toList? = some a ∧ ∀ x ∈ a, p x

@[simp, grind .]
theorem SortedSet.all_never {α cmp p} : ¬ SortedSet.All p (.never : SortedSet α cmp) := by
  simp [All]

@[simp, grind .]
theorem SortedSet.all_nil {α cmp p} : SortedSet.All p (.nil : SortedSet α cmp) := by
  simp [All]

@[simp, grind =]
theorem SortedSet.all_cons {α cmp p} {k t} :
    SortedSet.All p (.cons k t : SortedSet α cmp) ↔ p k ∧ ∀ x ∈ t.toList, p x := by
  simp [All]

@[simp, grind =]
theorem SortedSet.all_insert {α cmp p} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x : SortedSet α cmp} {k : α} (h : x.WF) :
    SortedSet.All p (x.insert k) ↔ x.All p ∧ p k := by
  cases x <;> grind [= insert, = All]

@[simp, grind =]
theorem SortedSet.all_merge {α cmp p} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {x y : SortedSet α cmp} (hx : x.WF) (hy : y.WF) :
    SortedSet.All p (x.merge y) ↔ x.All p ∧ y.All p := by
  cases x <;> cases y <;> grind [= merge, = All]

mutual

def FlattenedLevel.evalAssocList (f : Name → Nat) :
    SortedAssocList Name Nat Name.quickCmp → Nat
  | .nil => 0
  | .cons k v t => Max.max (f k + v) (FlattenedLevel.evalAssocList f t)
termination_by x => sizeOf x

def Conditional.eval (f : Name → Nat) : Conditional → Nat
  | { level, conds } => if ∀ k ∈ conds.toList, f k = 0 then 0 else level.eval f
termination_by x => sizeOf x

def Conditional.evalList (f : Name → Nat) : List Conditional → Nat
  | [] => 0
  | k :: t => Max.max (k.eval f) (Conditional.evalList f t)
termination_by x => sizeOf x

def FlattenedLevel.eval (f : Name → Nat) : FlattenedLevel → Nat
  | x =>
    Max.max (Max.max x.constOff (FlattenedLevel.evalAssocList f x.paramOff)) (Conditional.evalList f x.extra)
termination_by x => sizeOf x
decreasing_by rename_i a; cases a; decreasing_tactic

end

@[simp]
theorem FlattenedLevel.evalAssocList_le_iff
    {f : Name → Nat} {x : SortedAssocList Name Nat Name.quickCmp} {n : Nat} :
    evalAssocList f x ≤ n ↔ ∀ k v, (k, v) ∈ x.toList → f k + v ≤ n := by
  fun_induction evalAssocList with grind

@[simp]
theorem Conditional.evalList_le_iff
    {f : Name → Nat} {x : List Conditional} {n : Nat} :
    evalList f x ≤ n ↔ ∀ c, c ∈ x → c.eval f ≤ n := by
  induction x with simp [Conditional.evalList] <;> grind

@[simp]
theorem Conditional.eval_le_iff
    {f : Name → Nat} {x : Conditional} {n : Nat} :
    eval f x ≤ n ↔ ∀ k, k ∈ x.conds.toList → f k ≠ 0 → x.level.eval f ≤ n := by
  cases x
  rw [eval]
  split <;> grind

theorem FlattenedLevel.eval_le_iff
    {f : Name → Nat} {x : FlattenedLevel} {n : Nat} :
    eval f x ≤ n ↔ x.constOff ≤ n ∧ (∀ k v, (k, v) ∈ x.paramOff.toList → f k + v ≤ n) ∧
      ∀ c ∈ x.extra, ∀ k, k ∈ c.conds.toList → f k ≠ 0 → c.level.eval f ≤ n := by
  cases x
  rw [eval]
  simp [Nat.max_le]

theorem FlattenedLevel.eval_eq_zero_iff
    {f : Name → Nat} {x : FlattenedLevel} :
    eval f x = 0 ↔ x.constOff = 0 ∧ (∀ k v, (k, v) ∈ x.paramOff.toList → f k = 0 ∧ v = 0) ∧
      ∀ c ∈ x.extra, ∀ k, k ∈ c.conds.toList → f k ≠ 0 → c.level.eval f = 0 := by
  rw [← Nat.le_zero, eval_le_iff]
  simp

@[grind! .]
theorem FlattenedLevel.constOff_le_eval
    {f : Name → Nat} {x : FlattenedLevel} :
    x.constOff ≤ eval f x := by grind [= eval]

@[simp, grind =]
def _root_.Lean.Level.eval (f : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => l.eval f + 1
  | .max l l' => Max.max (l.eval f) (l'.eval f)
  | .imax l l' => Lean.Nat.imax (l.eval f) (l'.eval f)
  | .param nm | .mvar ⟨nm⟩ => f nm

theorem Nat.eq_of_forall_le_iff {a b : Nat} (h : ∀ c, a ≤ c ↔ b ≤ c) : a = b := by
  apply Nat.le_antisymm <;> simp [h, ← h]

@[simp, grind =]
theorem FlattenedLevel.eval_addExtra
    {f : Name → Nat} {x : FlattenedLevel} {c : Conditional} :
    eval f (x.addExtra c) = Max.max (eval f x) (c.eval f) := by
  apply Nat.eq_of_forall_le_iff
  intro c
  rw [FlattenedLevel.eval_le_iff, Nat.max_le, FlattenedLevel.eval_le_iff]
  simp [addExtra]
  grind

@[simp, grind =]
theorem FlattenedLevel.eval_const {off : Nat} :
    eval f { constOff := off } = off := by
  simp [FlattenedLevel.eval]

mutual

@[grind intro]
inductive Conditional.WF : Conditional → Prop where
  | intro (level_wf : x.level.WF) (conds_wf : x.conds.WF)
    (conds_ne_nil : x.conds ≠ .nil) : Conditional.WF x

@[grind intro]
inductive FlattenedLevel.WF : FlattenedLevel → Prop where
  | intro
    (constOff_le : ∀ k v, (k, v) ∈ x.paramOff.toList → v ≤ x.constOff)
    (paramOff_wf : x.paramOff.WF)
    (conditional_wf : ∀ c ∈ x.extra, c.WF) :
    FlattenedLevel.WF x

end

@[grind →]
theorem FlattenedLevel.WF.conditional_wf (h : WF x) {c} (hc : c ∈ x.extra) : c.WF := by
  cases h; solve_by_elim

@[grind →]
theorem FlattenedLevel.WF.constOff_le (h : WF x) {e} (he : e ∈ x.paramOff.toList) :
    e.2 ≤ x.constOff := by cases h; solve_by_elim

@[grind →]
theorem FlattenedLevel.WF.paramOff_wf (h : WF x) :
    x.paramOff.WF := by cases h; solve_by_elim

@[grind →]
theorem Conditional.WF.level_wf (h : WF x) : x.level.WF := by cases h; solve_by_elim

@[grind .]
theorem Conditional.WF.conds_wf (h : WF x) : x.conds.WF := by cases h; solve_by_elim

def SortedSetNode.any (x : SortedSetNode α cmp) (h : x ≠ .nil) : α :=
  match x with
  | .cons k _ => k

@[simp]
theorem SortedSetNode.any_mem (x : SortedSetNode α cmp) (h : x ≠ .nil) :
    x.any h ∈ x.toList := by cases x <;> simp_all [any] <;> simp_all

theorem Conditional.WF.conds_ne_nil (h : WF x) : x.conds ≠ .nil := by cases h; solve_by_elim

@[simp, grind =]
theorem FlattenedLevel.evalAssocList_insertMax
    {f : Name → Nat} {x : SortedAssocList Name Nat Name.quickCmp}
    {nm : Name} {off : Nat} (h : x.WF) :
    evalAssocList f (x.insertMax nm off) = Max.max (evalAssocList f x) (f nm + off) := by
  fun_induction SortedAssocList.insertMax with simp_all [evalAssocList] <;>
    grind [CompareOrder.cmp_eq (cmp := Name.quickCmp)]

@[simp, grind =]
theorem FlattenedLevel.evalAssocList_merge
    {f : Name → Nat} {x y : SortedAssocList Name Nat Name.quickCmp} (h : x.WF) (hy : y.WF) :
    evalAssocList f (x.merge y) = Max.max (evalAssocList f x) (evalAssocList f y) := by
  fun_induction SortedAssocList.merge with simp_all [evalAssocList] <;>
    grind [CompareOrder.cmp_eq (cmp := Name.quickCmp)]

@[simp, grind =]
theorem Conditional.evalList_apend
    {f : Name → Nat} {x y : List Conditional} :
    evalList f (x ++ y) = Max.max (evalList f x) (evalList f y) := by
  induction x generalizing y with simp_all [evalList] <;> grind

@[simp, grind =]
theorem FlattenedLevel.eval_addParam
    {f : Name → Nat} {x : FlattenedLevel} {nm : Name} {off : Nat} (h : x.WF) :
    eval f (x.addParam nm off) = Max.max (eval f x) (f nm + off) := by
  simp [eval, addParam, FlattenedLevel.evalAssocList_insertMax, h.paramOff_wf]
  lia

@[grind .]
protected theorem FlattenedLevel.WF.addExtra {x : FlattenedLevel} {c : Conditional}
    (hx : x.WF) (hc : c.WF) : (x.addExtra c).WF := by
  grind [= addExtra]

@[grind .]
protected theorem FlattenedLevel.WF.addParam {x : FlattenedLevel} {k : Name} {off : Nat}
    (hx : x.WF) (hoff : off ≤ x.constOff) : (x.addParam k off).WF := by
  grind [= addParam, cases FlattenedLevel.WF]

@[grind =]
theorem FlattenedLevel.constOff_addParam {x : FlattenedLevel} {k : Name} {off : Nat} :
    (x.addParam k off).constOff = x.constOff := (rfl)

@[grind =]
theorem FlattenedLevel.constOff_addExtra {x : FlattenedLevel} {c : Conditional} :
    (x.addExtra c).constOff = x.constOff := (rfl)

@[grind =]
def _root_.Lean.Level.zeroCheck (f : Name → Prop) : Level → Prop
  | .zero => True
  | .param nm | .mvar ⟨nm⟩ => f nm
  | .max u v => u.zeroCheck f ∧ v.zeroCheck f
  | .imax _ v => v.zeroCheck f
  | .succ _ => False

theorem _root_.Lean.Level.eval_eq_zero_iff {f : Name → Nat} {l : Level} :
    l.eval f = 0 ↔ l.zeroCheck (f · = 0) := by
  induction l with simp_all [Nat.imax, Level.zeroCheck]

theorem Nat.imax_eq' : Nat.imax n m = if m ≠ 0 then Max.max n m else 0 := by simp [Nat.imax]

theorem Level.flattenAux_spec {l : Level} {off : Nat} {acc : FlattenedLevel}
    {zc : SortedSet Name Name.quickCmp} (h : Level.flattenAux l off acc zc = (x, zc'))
    (hacc : acc.WF) (hzc : zc.WF) (hoff : off ≤ acc.constOff) :
    x.WF ∧ off ≤ x.constOff ∧ (∀ f, x.eval f = Max.max (l.eval f + off) (acc.eval f)) ∧
      zc'.WF ∧ ∀ f, zc'.All f ↔ zc.All f ∧ l.zeroCheck f := by
  classical
  fun_induction Level.flattenAux generalizing x zc' with
  | case1 off acc zc => grind
  | case2 off acc zc l h ih => grind [= FlattenedLevel.eval]
  | case3 off acc zc l h ih => grind
  | case4 => grind
  | case5 off acc zc l l' acc' hacc' ih ih' =>
    specialize ih hacc' (by grind) (by grind) hoff
    specialize ih' h (by grind) (by grind) (by lia)
    have zero_right : ∀ f, ¬Level.zeroCheck f l' := by simpa using ih.2.2.2.2
    refine ⟨ih'.1, ?_, ?_, ?_⟩
    · grind
    · simp [Nat.imax, Level.eval_eq_zero_iff]
      grind
    · grind
  | case6 off acc zc l l' acc' hacc' ih =>
    specialize ih hacc' (by grind) (by grind) hoff
    cases h
    have zero_right : ∀ f, Level.zeroCheck f l' := by simpa using ih.2.2.2.2
    refine ⟨by grind, ?_, ?_, ?_⟩
    · grind [cases FlattenedLevel.WF]
    · simp [Nat.imax, zero_right, ih, FlattenedLevel.eval, Level.eval_eq_zero_iff.mpr]
    · grind
  | case7 off acc zs l l' acc' k t hkt ih ih' =>
    specialize ih hkt (by grind) (by grind) (by lia)
    specialize ih' rfl (by grind) (by simp) (by lia)
    have hacc' : acc'.WF := by grind
    have zero_right : ∀ f, (f k ∧ ∀ (x : Name), x ∈ t.toList → f x) ↔ Level.zeroCheck f l' := by
      simpa using ih.2.2.2.2
    refine ⟨by grind, by grind, ?_, ?_⟩
    · intro f
      cases h
      have := @Level.eval_eq_zero_iff f l'
      simp [Nat.imax_eq', Conditional.eval]
      grind [= Conditional.eval]
    · grind
  | case8 off acc zc nm => grind
  | case9 off acc => grind

@[simp, grind .]
theorem Level.wf_flatten (l : Level) : (flatten l).WF := by
  grind [= flatten, flattenAux_spec rfl]

@[simp, grind =]
theorem Level.eval_flatten (l : Level) (f : Name → Nat) : (flatten l).eval f = l.eval f := by
  rw [flatten, (flattenAux_spec rfl _ _ _).2.2.1] <;> grind

mutual

@[grind =]
def Conditional.splitVars (l : Conditional) : List Name :=
  l.conds.toList ++ l.level.splitVars
termination_by sizeOf l
decreasing_by cases l; decreasing_tactic

def FlattenedLevel.splitVars (l : FlattenedLevel) : List Name :=
  l.extra.flatMap (·.splitVars)
termination_by sizeOf l
decreasing_by cases l; decreasing_tactic

end

theorem FlattenedLevel.max_evalAssocList_erase {f : Name → Nat}
    {x : SortedAssocList Name Nat Name.quickCmp} {k : Name}
    (hx : x.WF) (h : ∀ e ∈ x.toList, e.2 ≤ n) :
    Max.max n (FlattenedLevel.evalAssocList f (x.erase k)) =
      Max.max n (FlattenedLevel.evalAssocList (fun x => if x = k then 0 else f x) x) := by
  refine Nat.eq_of_forall_le_iff fun c => ?_
  simp [Nat.max_le, SortedAssocList.mem_erase, *]
  grind

theorem SortedSetNode.erase_eq_nil_iff {α cmp} [Std.LawfulEqCmp cmp]
    {x : SortedSetNode α cmp} {k : α} :
    SortedSetNode.erase k x = .nil ↔ x = .nil ∨ x = .cons k .nil := by
  rcases x with _ | ⟨_, _ | _⟩ <;> grind [= erase]

mutual

theorem FlattenedLevel.setZero_spec {l : FlattenedLevel} (h : l.WF) (key : Name) :
    (setZero l key).WF ∧
      ∀ f, (setZero l key).eval f = l.eval (fun x => if x = key then 0 else f x) := by
  rw [setZero]
  have := setZero.go_spec h (newExtra := []) @h.conditional_wf nofun key
  constructor
  · exact this.1
  · intro f
    simp [this, eval]
termination_by sizeOf l
decreasing_by cases l; decreasing_tactic

theorem FlattenedLevel.setZero.go_spec {newExtra iter} {l : FlattenedLevel}
    (hl : l.WF) (hiter : ∀ x ∈ iter, x.WF) (hne : ∀ x ∈ newExtra, x.WF) (key : Name) :
    (setZero.go l key newExtra iter).WF ∧
      ∀ f, (setZero.go l key newExtra iter).eval f =
        Max.max (Max.max l.constOff (evalAssocList (fun x => if x = key then 0 else f x) l.paramOff))
          (Max.max (Conditional.evalList f newExtra)
            (Conditional.evalList (fun x => if x = key then 0 else f x) iter)) := by
  match iter with
  | [] =>
    simp [setZero.go]
    grind [= FlattenedLevel.eval, FlattenedLevel.max_evalAssocList_erase]
  | ⟨l', c⟩ :: tail =>
    simp only [setZero.go]
    have ih := @setZero.go_spec (iter := tail) (hl := hl) (hiter := by grind) (key := key)
    specialize hiter _ List.mem_cons_self
    have := hiter.conds_wf
    split
    · rename_i herase
      simp only [SortedSetNode.erase_eq_nil_iff] at herase
      grind [= Conditional.evalList, = Conditional.eval]
    · have ih' := setZero_spec (l := l') hiter.level_wf key
      grind (splits := 20) [= Conditional.evalList, = Conditional.eval]
termination_by sizeOf iter

end

@[grind .]
theorem FlattenedLevel.WF.setZero {l : FlattenedLevel} (h : l.WF) (key : Name) :
    (setZero l key).WF := by
  grind [setZero_spec]

@[grind =]
theorem FlattenedLevel.eval_setZero {l : FlattenedLevel} (h : l.WF) (key : Name) :
    ∀ f, (setZero l key).eval f = l.eval (fun x => if x = key then 0 else f x) := by
  grind [setZero_spec]

theorem fn_eq_zero_or_max_one [DecidableEq α] (f : α → Nat) (key : α) :
    f = (fun x => if x = key then 0 else f x) ∨
      f = (fun x => if x = key then Max.max 1 (f x) else f x) := by grind

@[grind .]
protected theorem FlattenedLevel.WF.merge {l l' : FlattenedLevel} (hl : l.WF) (hl' : l'.WF) :
    (l.merge l').WF := by
  constructor <;> simp [merge, ← SortedAssocList.find?_eq_some_iff,
    hl.paramOff_wf.merge hl'.paramOff_wf, or_imp, eq_true hl.conditional_wf,
    eq_true hl'.conditional_wf, SortedAssocList.find?_merge hl.paramOff_wf hl'.paramOff_wf,
    Option.max_eq_some_iff, Option.eq_none_iff_forall_ne_some]
  simp [SortedAssocList.find?_eq_some_iff, hl.paramOff_wf, hl'.paramOff_wf]
  grind

@[grind =]
protected theorem FlattenedLevel.eval_merge {l l' : FlattenedLevel} {f : Name → Nat}
    (hl : l.WF) (hl' : l'.WF) : (l.merge l').eval f = Max.max (l.eval f) (l'.eval f) := by
  simp [merge, FlattenedLevel.eval, hl.paramOff_wf, hl'.paramOff_wf]
  ac_rfl

theorem FlattenedLevel.max_evalAssocList_const_subst {n : Nat}
    {p : SortedAssocList Name Nat Name.quickCmp} {f : Name → Nat}
    (hp : p.WF) (h : ∀ e ∈ p.toList, e.2 ≤ n) :
    Max.max n (evalAssocList (fun x => if x = key then Max.max 1 (f x) else f x) p) =
      Max.max (match p.find? key with
          | none => n
          | some off => Max.max n (off + 1)) (evalAssocList f p) := by
  refine Nat.eq_of_forall_le_iff fun c => ?_
  simp only [Nat.max_le, evalAssocList_le_iff]
  split
  · grind
  · rename_i hfind
    rw [SortedAssocList.find?_eq_some_iff hp] at hfind
    grind

mutual

theorem FlattenedLevel.setNonzero_spec {l : FlattenedLevel} (h : l.WF) (key : Name) :
    (setNonzero l key).WF ∧
      ∀ f, (setNonzero l key).eval f = l.eval (fun x => if x = key then Max.max 1 (f x) else f x) := by
  unfold setNonzero
  extract_lets l'
  have hl' : l'.extra = l.extra := by grind
  have ⟨wf, eval⟩ := setNonzero.go_spec (l := { l' with extra := [] }) (iter := l'.extra)
    (by grind) (by grind) key
  refine ⟨wf, ?_⟩
  intro f
  rw [eval, FlattenedLevel.eval, FlattenedLevel.eval, Conditional.evalList, hl']
  simp only [Nat.zero_le, Nat.max_eq_left]
  congr 1
  rw [FlattenedLevel.max_evalAssocList_const_subst (by grind) (by grind)]
  grind
termination_by sizeOf l
decreasing_by cases l; grind

theorem FlattenedLevel.setNonzero.go_spec {iter} {l : FlattenedLevel}
    (hl : l.WF) (hiter : ∀ x ∈ iter, x.WF) (key : Name) :
    (setNonzero.go key l iter).WF ∧
      ∀ f, (setNonzero.go key l iter).eval f = Max.max (l.eval f)
          (Conditional.evalList (fun x => if x = key then Max.max 1 (f x) else f x) iter) := by
  match iter with
  | [] => simp [setNonzero.go, hl]
  | ⟨l', c⟩ :: tail =>
    have ih := @setNonzero.go_spec (iter := tail) (hiter := by grind) (key := key)
    specialize hiter _ List.mem_cons_self
    simp only [setNonzero.go, SortedSetNode.contains_iff_mem hiter.conds_wf]
    have := hiter.level_wf
    have := hiter.conds_wf
    have := hiter.conds_ne_nil
    have ih' := setNonzero_spec (l := l') hiter.level_wf key
    grind [= Conditional.evalList, = Conditional.eval]
termination_by sizeOf iter

end

@[grind .]
theorem FlattenedLevel.WF.setNonzero {l : FlattenedLevel} (h : l.WF) (key : Name) :
    (setNonzero l key).WF := by
  grind [setNonzero_spec]

@[grind =]
theorem FlattenedLevel.eval_setNonzero {l : FlattenedLevel} (h : l.WF) (key : Name) :
    ∀ f, (setNonzero l key).eval f = l.eval (fun x => if x = key then Max.max 1 (f x) else f x) := by
  grind [setNonzero_spec]

@[grind =]
theorem FlattenedLevel.splitVars_merge {l l' : FlattenedLevel} :
    x ∈ (l.merge l').splitVars ↔ x ∈ l.splitVars ∨ x ∈ l'.splitVars := by
  simp [splitVars, merge]

@[grind =]
theorem FlattenedLevel.splitVars_addExtra {l : FlattenedLevel} {c} :
    x ∈ (l.addExtra c).splitVars ↔ x ∈ l.splitVars ∨ x ∈ c.splitVars := by
  simp [splitVars, addExtra]
  grind

mutual

theorem FlattenedLevel.splitVars_setZero {l : FlattenedLevel} {key : Name}
    (h : l.WF) (hx : x ∈ (setZero l key).splitVars) :
    x ∈ l.splitVars ∧ x ≠ key := by
  rw [setZero] at hx
  simpa [splitVars] using setZero.splitVars_go (hx := hx) h (by grind) (by grind)
termination_by sizeOf l
decreasing_by cases l; decreasing_tactic

theorem FlattenedLevel.setZero.splitVars_go {newExtra iter} {l : FlattenedLevel}
    (hl : l.WF) (hiter : ∀ x ∈ iter, x.WF) (hne : ∀ x ∈ newExtra, x.WF) (key : Name)
    (hx : x ∈ (setZero.go l key newExtra iter).splitVars) :
    ((x ∈ l.splitVars ∨ ∃ a ∈ iter, x ∈ a.splitVars) ∧ x ≠ key) ∨
      ∃ a ∈ newExtra, x ∈ a.splitVars := by
  match iter with
  | [] => simp [setZero.go, splitVars] at *; grind
  | ⟨l', c⟩ :: tail =>
    rw [setZero.go] at hx
    have ih := @setZero.splitVars_go (iter := tail) (key := key) (hiter := by grind)
    have ih' := @splitVars_setZero (l := l') (key := key)
    specialize hiter _ List.mem_cons_self
    have := hiter.conds_wf
    split at hx
    · grind
    · specialize ih _ _ _ hl (by grind) hx
      simp [Conditional.splitVars, SortedSetNode.mem_erase, *] at ih ⊢
      grind
termination_by sizeOf iter

end

mutual

theorem FlattenedLevel.splitVars_setNonzero {l : FlattenedLevel} {key : Name}
    (h : l.WF) (hx : x ∈ (setNonzero l key).splitVars) :
    x ∈ l.splitVars ∧ x ≠ key := by
  unfold setNonzero at hx
  extract_lets l' at hx
  have := setNonzero.splitVars_go (hx := hx) (by grind) (by grind) key
  simp [splitVars] at this ⊢
  grind
termination_by sizeOf l
decreasing_by cases l; grind

theorem FlattenedLevel.setNonzero.splitVars_go {iter} {l : FlattenedLevel}
    (hl : l.WF) (hiter : ∀ x ∈ iter, x.WF) (key : Name)
    (hx : x ∈ (setNonzero.go key l iter).splitVars) :
    x ∈ l.splitVars ∨ ((∃ a ∈ iter, x ∈ a.splitVars) ∧ x ≠ key) := by
  match iter with
  | [] => simpa [setNonzero.go, splitVars] using hx
  | ⟨l', c⟩ :: tail =>
    rw [setNonzero.go] at hx
    have ih := @setNonzero.splitVars_go (iter := tail) (key := key) (hiter := by grind)
    specialize hiter _ List.mem_cons_self
    have := hiter.conds_wf
    have := hiter.conds_ne_nil
    have := hiter.level_wf
    have ih' := @splitVars_setNonzero (l := l') (key := key) (x := x) this
    simp [Conditional.splitVars] at *
    grind
termination_by sizeOf iter

end

theorem FlattenedLevel.eval_zero (hl : WF l) : l.eval (fun _ => 0) = l.constOff := by
  simp only [eval, Conditional.evalList_le_iff, Conditional.eval_le_iff, ne_eq, not_true_eq_false,
    Nat.max_assoc, false_implies, implies_true, Nat.max_eq_left]
  apply Nat.max_eq_left
  simp; grind

theorem FlattenedLevel.eval_single (hl : WF l) (he : l.extra = []) :
    l.eval (fun a => if a = b then c else 0) =
      match l.paramOff.find? b with
      | none => l.constOff
      | some v => Max.max l.constOff (v + c) := by
  refine Nat.eq_of_forall_le_iff fun c' => ?_
  rw [eval_le_iff, he]
  simp only [List.not_mem_nil, ne_eq, ite_eq_right_iff, not_imp, and_imp, false_implies,
    implies_true, and_true]
  split
  · rename_i h
    simp only [Option.eq_none_iff_forall_ne_some, ne_eq,
      SortedAssocList.find?_eq_some_iff hl.paramOff_wf] at h
    grind
  · rename_i h
    simp only [SortedAssocList.find?_eq_some_iff hl.paramOff_wf] at h
    grind

theorem FlattenedLevel.find?_paramOff_of_extra (hl : WF l) (he : l.extra = []) :
    l.paramOff.find? k =
      letI e := l.eval (fun a => if a = k then l.constOff + 1 else 0)
      if e = l.constOff then none else some (e - l.constOff - 1) := by
  rw [eval_single hl he]
  grind

deriving instance ReflBEq, LawfulBEq for SortedAssocList

theorem FlattenedLevel.forall_eval_split {l l' : FlattenedLevel} :
    (∀ f, l.eval f = l'.eval f) ↔
      (∀ f : Name → Nat, l.eval (fun x => if x = key then 0 else f x) =
        l'.eval (fun x => if x = key then 0 else f x)) ∧
      (∀ f : Name → Nat, l.eval (fun x => if x = key then Max.max 1 (f x) else f x) =
        l'.eval (fun x => if x = key then Max.max 1 (f x) else f x)) := by
  constructor
  · grind
  · intro ⟨hz, hnz⟩ f
    by_cases h : f key = 0
    · refine cast ?_ (hz f)
      congr <;> grind
    · refine cast ?_ (hnz f)
      congr <;> grind

theorem _root_.Std.ExtTreeSet.size_le_of_subset
    {cmp} [Std.TransCmp cmp] {a b : Std.ExtTreeSet α cmp}
    (h : ∀ k, k ∈ a → k ∈ b) : a.size ≤ b.size := by
  have : a = a.inter b := by
    apply Std.ExtTreeSet.ext_get?
    simp_all [Std.ExtTreeSet.inter_eq, Std.ExtTreeSet.get?_inter]
    intro k h'
    by_cases h : (a.get? k).isSome
    · simp_all
    · rw [Option.not_isSome_iff_eq_none] at h
      exact h
  rw [this]
  exact Std.ExtTreeSet.size_inter_le_size_right

theorem _root_.Std.ExtTreeSet.size_lt_of_subset
    {cmp} [Std.TransCmp cmp] {a b : Std.ExtTreeSet α cmp}
    (h : ∀ k, k ∈ a → k ∈ b) (ha : k ∉ a) (hb : k ∈ b) : a.size < b.size := by
  suffices (a.insert k).size ≤ b.size by
    simpa [Std.ExtTreeSet.size_insert, ha, Nat.add_one_le_iff] using this
  refine Std.ExtTreeSet.size_le_of_subset (a := a.insert k) ?_
  intro k
  simp only [Std.ExtTreeSet.mem_insert]
  rintro (h | h)
  · rwa [← Std.ExtTreeSet.mem_congr h]
  · solve_by_elim

theorem FlattenedLevel.beq_iff (hl : WF l) (hl' : WF l') :
    FlattenedLevel.beq l l' ↔ ∀ f, l.eval f = l'.eval f := by
  rw [beq]
  simp only [bne_iff_ne, ne_eq,
    bind_pure_comp, ite_not]
  split
  rotate_left
  · simp only [Id.run_pure, Bool.false_eq_true, false_iff]
    intro h
    specialize h fun _ => 0
    simp [FlattenedLevel.eval_zero, *] at h
  split
  · rename_i a _ ha
    replace ha : a ∈ l.extra := by grind
    have := hl.conditional_wf ha
    have := this.conds_ne_nil
    match heq : a.conds, this with | .cons cond t, _ => ?_
    simp only [Id.run_pure, Bool.and_eq_true]
    rw [beq_iff (by grind) (by grind), beq_iff (by grind) (by grind)]
    simp only [eval_setZero, eval_setNonzero, hl, hl', ← FlattenedLevel.forall_eval_split]
  split
  · rename_i a _ ha
    replace ha : a ∈ l'.extra := by grind
    have := hl'.conditional_wf ha
    have := this.conds_ne_nil
    match heq : a.conds, this with | .cons cond t, _ => ?_
    simp only [Id.run_pure, Bool.and_eq_true]
    rw [beq_iff (by grind) (by grind), beq_iff (by grind) (by grind)]
    simp only [eval_setZero, eval_setNonzero, hl, hl', ← FlattenedLevel.forall_eval_split]
  have : l.extra = [] := by cases h : l.extra <;> grind
  have : l'.extra = [] := by cases h : l'.extra <;> grind
  simp only [Id.run_pure, beq_iff_eq]
  constructor
  · intro h
    have : l = l' := by cases l; cases l'; simp_all
    simp [this]
  · intro hf
    apply SortedAssocList.ext hl.paramOff_wf hl'.paramOff_wf
    intro k
    rw [FlattenedLevel.find?_paramOff_of_extra hl ‹_›,
      FlattenedLevel.find?_paramOff_of_extra hl' ‹_›]
    simp [*]
termination_by
  (Std.ExtTreeSet.ofList l.splitVars Name.quickCmp).size +
    (Std.ExtTreeSet.ofList l'.splitVars Name.quickCmp).size
decreasing_by
  · apply Nat.add_lt_add_of_lt_of_le
    · apply Std.ExtTreeSet.size_lt_of_subset (k := cond)
      · intro k hk
        simp only [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
        exact (splitVars_setZero hl hk).1
      · intro hk
        simp only [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
        simpa using (splitVars_setZero hl hk).2
      · simp [splitVars, *]
        simp [Conditional.splitVars, *]
    · apply Std.ExtTreeSet.size_le_of_subset
      intro k hk
      simp at hk ⊢
      exact (splitVars_setZero hl' hk).1
  · apply Nat.add_lt_add_of_lt_of_le
    · apply Std.ExtTreeSet.size_lt_of_subset (k := cond)
      · intro k hk
        simp only [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
        exact (splitVars_setNonzero hl hk).1
      · intro hk
        simp only [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
        simpa using (splitVars_setNonzero hl hk).2
      · simp [splitVars, *]
        simp [Conditional.splitVars, *]
    · apply Std.ExtTreeSet.size_le_of_subset
      intro k hk
      simp at hk ⊢
      exact (splitVars_setNonzero hl' hk).1
  · apply Nat.add_lt_add_of_le_of_lt
    · apply Std.ExtTreeSet.size_le_of_subset
      intro k hk
      simp at hk ⊢
      exact (splitVars_setZero hl hk).1
    · apply Std.ExtTreeSet.size_lt_of_subset (k := cond)
      · intro k hk
        simp only [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
        exact (splitVars_setZero hl' hk).1
      · intro hk
        simp only [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
        simpa using (splitVars_setZero hl' hk).2
      · simp [splitVars, *]
        simp [Conditional.splitVars, *]
  · apply Nat.add_lt_add_of_le_of_lt
    · apply Std.ExtTreeSet.size_le_of_subset
      intro k hk
      simp at hk ⊢
      exact (splitVars_setNonzero hl hk).1
    · apply Std.ExtTreeSet.size_lt_of_subset (k := cond)
      · intro k hk
        simp only [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
        exact (splitVars_setNonzero hl' hk).1
      · intro hk
        simp only [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
        simpa using (splitVars_setNonzero hl' hk).2
      · simp [splitVars, *]
        simp [Conditional.splitVars, *]

theorem Level.isEquivComplete_iff {l l' : Level} :
    l.flatten.beq l'.flatten ↔ l.eval = l'.eval := by
  simp [funext_iff, FlattenedLevel.beq_iff]
