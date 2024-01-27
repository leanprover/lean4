/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Json
import Lean.Data.NameMap
import Lake.Util.DRBMap
import Lake.Util.RBArray
import Lake.Util.Compare

open Lean

namespace Lake

export Lean (Name NameMap)

@[inline] def NameMap.empty : NameMap α := RBMap.empty

instance : ForIn m (NameMap α) (Name × α) where
  forIn self init f := self.forIn init f

instance : Coe (RBMap Name α Name.quickCmp) (NameMap α) := ⟨id⟩

abbrev OrdNameMap α := RBArray Name α Name.quickCmp
@[inline] def OrdNameMap.empty : OrdNameMap α := RBArray.empty
@[inline] def mkOrdNameMap (α : Type) : OrdNameMap α := RBArray.empty

abbrev DNameMap α := DRBMap Name α Name.quickCmp
@[inline] def DNameMap.empty : DNameMap α := DRBMap.empty

instance [ToJson α] : ToJson (NameMap α) where
  toJson m := Json.obj <| m.fold (fun n k v => n.insert compare k.toString (toJson v)) .leaf

instance [FromJson α] : FromJson (NameMap α) where
  fromJson? j := do
    (← j.getObj?).foldM (init := {}) fun m k v =>
      let k := k.toName
      if k.isAnonymous then
        throw "expected name"
      else
        return m.insert k (← fromJson? v)

/-! # Name Helpers -/

namespace Name
open Lean.Name

abbrev IsSimple : Name → Prop
| .str .anonymous _ => True
| _ => False

@[simp] protected theorem beq_false (m n : Name) : (m == n) = false ↔ ¬ (m = n) := by
  rw [← beq_iff_eq m n]; cases m == n <;> simp (config := { decide := true })

@[simp] theorem isPrefixOf_self {n : Name} : n.isPrefixOf n := by
  cases n <;> simp [isPrefixOf]

@[simp] theorem isPrefixOf_append {n m : Name} : ¬ n.hasMacroScopes → ¬ m.hasMacroScopes → n.isPrefixOf (n ++ m) := by
  intro h1 h2
  show n.isPrefixOf (n.append m)
  simp_all [Name.append]
  clear h2; induction m <;> simp [*, Name.appendCore, isPrefixOf]

@[simp] theorem quickCmpAux_iff_eq : ∀ {n n'}, quickCmpAux n n' = .eq ↔ n = n'
| .anonymous, n => by cases n <;> simp [quickCmpAux]
| n, .anonymous => by cases n <;> simp [quickCmpAux]
| .num .., .str .. => by simp [quickCmpAux]
| .str .., .num .. => by simp [quickCmpAux]
| .num p₁ n₁, .num p₂ n₂ => by
  simp only [quickCmpAux]; split <;>
  simp_all [quickCmpAux_iff_eq, show ∀ p, (p → False) ↔ ¬ p from fun _ => .rfl]
| .str p₁ s₁, .str p₂ s₂ => by
  simp only [quickCmpAux]; split <;>
  simp_all [quickCmpAux_iff_eq, show ∀ p, (p → False) ↔ ¬ p from fun _ => .rfl]

instance : LawfulCmpEq Name quickCmpAux where
  eq_of_cmp := quickCmpAux_iff_eq.mp
  cmp_rfl := quickCmpAux_iff_eq.mpr rfl

theorem eq_of_quickCmp {n n' : Name} : n.quickCmp n' = .eq → n = n' := by
  unfold Name.quickCmp
  intro h_cmp; split at h_cmp
  next => exact eq_of_cmp h_cmp
  next => contradiction

theorem quickCmp_rfl {n : Name} : n.quickCmp n = .eq := by
  unfold Name.quickCmp
  split <;> exact cmp_rfl

instance : LawfulCmpEq Name Name.quickCmp where
  eq_of_cmp := eq_of_quickCmp
  cmp_rfl := quickCmp_rfl

open Syntax

def quoteFrom (ref : Syntax) : Name → Term
| .anonymous => mkCIdentFrom ref ``anonymous
| .str p s => mkApp (mkCIdentFrom ref ``mkStr) #[quoteFrom ref p, quote s]
| .num p v => mkApp (mkCIdentFrom ref ``mkNum) #[quoteFrom ref p, quote v]

end Name

/--
A subtype of `Lean.Name` that is provably "simple".
That is, a single-part string name (i.e., `Lean.Name.mkSimple`).

The primary advantage of this type over a plain `String` is that it
comes with a precomputed `hash` value for quick equality comparisons and
can be cast into a normal `Name` as a no-op.
-/
def SimpleName :=
  {n : Name // Name.IsSimple n}

namespace SimpleName

abbrev toName (n : SimpleName) : Name :=
  n.val

instance : Coe SimpleName Name := ⟨toName⟩
instance : Repr SimpleName := ⟨(·.toName.reprPrec ·)⟩

theorem toName_eq_of_eq {m n : SimpleName} :
  m = n → m.toName = n.toName
:= by simp_all

theorem toName_eq_iff_eq {m n : SimpleName} :
  m.toName = n.toName ↔ m = n
:= .intro Subtype.eq toName_eq_of_eq

abbrev ofName (n : Name) (h : Name.IsSimple n) : SimpleName :=
  ⟨n, h⟩

abbrev mk (s : String) : SimpleName :=
  ofName (.str .anonymous s) True.intro

instance : Inhabited SimpleName := ⟨mk default⟩

instance : Coe String SimpleName := ⟨mk⟩
instance : CoeDep Name (.str .anonymous s) SimpleName := ⟨mk s⟩

@[inline] protected def hash (n : SimpleName) : UInt64 :=
  n.toName.hash

instance : Hashable SimpleName := ⟨SimpleName.hash⟩

@[inline] def toString (n : SimpleName) : String :=
  match n with | ⟨.str _ s, _⟩ => s

instance : ToString SimpleName := ⟨toString⟩
instance : Coe SimpleName String := ⟨toString⟩

@[simp] theorem string_mk : toString (mk s) = s := rfl

theorem eq_of_toString_eq {n m : SimpleName} :
  m.toString = n.toString → m = n
:=
  match m, n with
  | ⟨.str .anonymous s, _⟩, ⟨.str .anonymous s', _⟩ =>
    by intros; simp_all

instance : ToJson SimpleName := ⟨(·.toString)⟩
instance : FromJson SimpleName := ⟨fun j => mk <$> j.getStr?⟩

protected abbrev beq (m n : SimpleName) : Bool :=
  m.toName == n.toName

instance : BEq SimpleName := ⟨SimpleName.beq⟩

protected theorem beq_iff_eq {m n : SimpleName} : m == n ↔ m = n := by
  simp only [BEq.beq]
  simp [SimpleName.beq, Name.beq_iff_eq, toName_eq_iff_eq]

instance : LawfulBEq SimpleName where
  eq_of_beq := SimpleName.beq_iff_eq.1
  rfl := SimpleName.beq_iff_eq.2 rfl

instance : DecidableEq SimpleName :=
  fun a b => if h : a == b then .isTrue (by simp_all) else .isFalse (by simp_all)

def quickCmp (n₁ n₂ : SimpleName) : Ordering :=
  match compare n₁.hash n₂.hash with
  | Ordering.eq => compare n₁.toString n₂.toString
  | ord => ord

theorem eq_of_quickCmp {n n' : SimpleName} : n.quickCmp n' = .eq → n = n' := by
  unfold SimpleName.quickCmp
  intro h_cmp; split at h_cmp
  next => exact eq_of_toString_eq <| eq_of_cmp h_cmp
  next => contradiction

theorem quickCmp_rfl {n : SimpleName} : n.quickCmp n = .eq := by
  unfold SimpleName.quickCmp
  split <;> exact cmp_rfl

instance : LawfulCmpEq SimpleName SimpleName.quickCmp where
  eq_of_cmp := eq_of_quickCmp
  cmp_rfl := quickCmp_rfl

end SimpleName

abbrev SimpleNameSet := RBTree SimpleName SimpleName.quickCmp
@[inline] def SimpleNameSet.empty : SimpleNameSet := RBTree.empty

abbrev SimpleNameMap (α : Type) := RBMap SimpleName α SimpleName.quickCmp
@[inline] def SimpleNameMap.empty : SimpleNameMap α := RBMap.empty
@[inline] def mkSimpleNameMap (α : Type) : SimpleNameMap α := RBMap.empty

instance [ToJson α] : ToJson (SimpleNameMap α) where
  toJson m := Json.obj <| m.fold (fun n k v => n.insert compare k.toString (toJson v)) .leaf

instance [FromJson α] : FromJson (SimpleNameMap α) where
  fromJson? j := do (← j.getObj?).foldM (init := {}) fun m k v =>
    return m.insert (SimpleName.mk k) (← fromJson? v)

abbrev DSimpleNameMap α := DRBMap SimpleName α SimpleName.quickCmp
@[inline] def SimpleNameMapempty : DNameMap α := DRBMap.empty

abbrev OrdSimpleNameMap α := RBArray SimpleName α SimpleName.quickCmp
@[inline] def OrdSimpleNameMap.empty : OrdNameMap α := RBArray.empty
