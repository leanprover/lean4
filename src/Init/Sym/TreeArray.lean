/-
Copyright (c) 2026 Robin Arnez. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module
prelude
public import Init.Data.Vector.Lemmas
import Init.Omega
import Init.Data.Bool
import Init.ByCases
import Init.Data.Nat.Mod
import Init.Data.List.Nat.Modify
import Init.Data.Array.Bootstrap

@[expose] public section

namespace Lean.Sym

/-- `FullBlock α n` is equivalent to `Vector α (2 ^ n)` -/
inductive FullBlock (α : Type u) : Nat → Type u where
  | single (x : α) : FullBlock α (nat_lit 0)
  | split {n : Nat} (l r : FullBlock α n) : FullBlock α n.succ
deriving Repr

/-- `PartialBlock α n` is equivalent to `{ xs : Array α // xs.size.size = n }` -/
inductive PartialBlock (α : Type u) : Nat → Type u where
  | empty : PartialBlock α (nat_lit 0)
  | split {n m : Nat} (l : FullBlock α n) (r : PartialBlock α m) (h : m.ble n) :
    PartialBlock α n.succ
deriving Repr

@[cbv_opaque, no_expose]
def FullBlock.toVector {α : Type u} {n : Nat} : FullBlock α n → Vector α (2 ^ n)
  | .single x => #v[x]
  | .split l r => (l.toVector ++ r.toVector).cast (by rw [Nat.two_pow_succ])

@[cbv_opaque, no_expose]
def PartialBlock.toArray {α : Type u} {n : Nat} : PartialBlock α n → Array α
  | .empty => #[]
  | .split l r h => l.toVector.toArray ++ r.toArray
-- use well-founded recursion to make sure the kernel is not going to unfold this meaningfully
termination_by x => sizeOf x

noncomputable abbrev FullBlock.prependList {α : Type u} {n : Nat} :
    FullBlock α n → List α → List α :=
  FullBlock.rec List.cons fun {_n} _l _r lih rih acc => lih (rih acc)

noncomputable abbrev PartialBlock.prependList {α : Type u} {n : Nat} :
    PartialBlock α n → List α → List α :=
  PartialBlock.rec (fun l => l) fun {_n _m} l _r _h ih acc => l.prependList (ih acc)

theorem PartialBlock.emptyWithCapacity_eq {α : Type u} {n : Nat} :
    Array.emptyWithCapacity n = (empty.toArray : Array α) := by simp [toArray]

theorem FullBlock.prependList_eq {α : Type u} {n : Nat} {b : FullBlock α n} {l : List α} :
    b.prependList l = b.toVector.toArray.toList ++ l := by
  induction b generalizing l <;> simp_all [prependList, toVector]

theorem PartialBlock.prependList_eq {α : Type u} {n : Nat} {b : PartialBlock α n} {l : List α} :
    b.prependList l = b.toArray.toList ++ l := by
  induction b generalizing l <;> simp_all [prependList, toArray, FullBlock.prependList_eq]

theorem PartialBlock.arrayMk_eq {α : Type u} {n : Nat} {l : List α} {b : PartialBlock α n}
    (h : b.prependList [] = l) : Array.mk l = b.toArray := by
  simp_all [prependList_eq, ← Array.toList_inj]

theorem PartialBlock.toList_toArray {α : Type u} {n : Nat} {b : PartialBlock α n} :
    b.toArray.toList = b.prependList [] := by
  simp_all [prependList_eq]

noncomputable abbrev FullBlock.get {α : Type u} {n : Nat}
    (x : FullBlock α n) (i : Nat) : α :=
  x.rec (fun a => a) fun {n} _l _r lih rih =>
    ((i.shiftRight n).mod (nat_lit 2)).rec lih fun _ _ => rih

noncomputable abbrev FullBlock.modify {α : Type u} {n : Nat}
    (x : FullBlock α n) (i : Nat) (f : α → α) : FullBlock α n :=
  x.rec (fun a => .single (f a)) fun {n} l r lih rih =>
    ((i.shiftRight n).mod (nat_lit 2)).rec (.split lih r) fun _ _ => .split l rih

noncomputable abbrev PartialBlock.get? {α : Type u} {n : Nat}
    (x : PartialBlock α n) : Nat → Option α :=
  x.rec (fun _ => none) fun {n _m} l _r _h ih i =>
    (((nat_lit 1).shiftLeft n).ble i).rec (some (l.get i))
      (ih (i.sub ((nat_lit 1).shiftLeft n)))

noncomputable abbrev PartialBlock.modify {α : Type u} {n : Nat}
    (x : PartialBlock α n) (f : α → α) : Nat → PartialBlock α n :=
  x.rec (fun _ => .empty) fun {n _m} l r h ih i =>
    (((nat_lit 1).shiftLeft n).ble i).rec (.split (l.modify i f) r h)
      (.split l (ih (i.sub ((nat_lit 1).shiftLeft n))) h)

inductive PushResult (α : Type u) (n : Nat) where
  | part (x : PartialBlock α n)
  | full (x : FullBlock α n)

noncomputable abbrev PartialBlock.push.full {α : Type u} {n m : Nat}
    (l : FullBlock α n) (h : m.ble n) (b : FullBlock α m) :
    PushResult α n.succ :=
  (m.succ.ble n).rec (motive := fun b => m.succ.ble n = b → _)
    (fun h =>
      haveI : m = n := by simp_all [← Bool.not_eq_true]; omega
      .full <| .split l (this.rec b))
    (fun h => .part <| .split l (.split b .empty (by simp)) h) rfl

noncomputable def PartialBlock.push {α : Type u} {n : Nat}
    (b : PartialBlock α n) (val : α) : PushResult α n :=
  b.rec (.full (.single val)) fun {_n _m} l _r h =>
    PushResult.rec (fun r => .part <| .split l r h) (push.full l h)

def PartialBlock.pushImpl {α : Type u} {n : Nat}
    (b : PartialBlock α n) (val : α) : PushResult α n :=
  match b with
  | .empty => .full (.single val)
  | @PartialBlock.split _ n m l r h =>
    match pushImpl r val with
    | .part x => .part <| .split l x h
    | .full x =>
      if h : m.succ.ble n then
        .part <| .split l (.split x .empty (by simp)) h
      else
        haveI : m = n := by simp_all; omega
        .full <| .split l (this.rec x)

@[csimp]
theorem PartialBlock.push_eq_pushImpl : @push = @pushImpl := by
  funext α n b val
  fun_induction pushImpl with simp_all [push, Bool.rec_dep_eq]

theorem PartialBlock.push_spec {α : Type u} {n : Nat} (b : PartialBlock α n) (v : α) :
    (match b.push v with | .part x => x.toArray | .full x => x.toVector.toArray) =
      b.toArray.push v := by
  rw [PartialBlock.push_eq_pushImpl]
  induction b with
  | empty => simp [PartialBlock.pushImpl, PartialBlock.toArray, FullBlock.toVector]
  | @split n m l r h ih =>
    simp only [Nat.succ_eq_add_one, PartialBlock.pushImpl]
    generalize r.pushImpl v = b at ih
    rcases b with b | b
    · simp_all [PartialBlock.toArray]
    · by_cases h : m + 1 ≤ n
      · simp_all [PartialBlock.toArray]
      · have : m = n := by simp_all; omega
        subst this
        simp_all [PartialBlock.toArray, -Nat.not_le, FullBlock.toVector]

theorem PartialBlock.push_part {α : Type u} {n : Nat} {b b' : PartialBlock α n} {v : α}
    (h : b.push v = .part b') : b.toArray.push v = b'.toArray := by
  rw [← push_spec, h]

theorem PartialBlock.push_full {α : Type u} {n : Nat}
    {b : PartialBlock α n} {b' : FullBlock α n} {v : α}
    (h : b.push v = .full b') : b.toArray.push v = (split b' empty (by simp)).toArray := by
  simp [← push_spec, h, PartialBlock.toArray]

noncomputable abbrev FullBlock.pop {α : Type u} {n : Nat} (b : FullBlock α n) : PartialBlock α n :=
  b.rec (fun _ => .empty) fun {_n} l _r _lih rih => .split l rih (by simp)

inductive PopResult (α : Type u) : Nat → Type u where
  | empty : PopResult α (nat_lit 0)
  | done {n : Nat} (x : PartialBlock α n) : PopResult α n
  | shrink {n : Nat} (x : PartialBlock α n) : PopResult α n.succ

noncomputable def PartialBlock.pop {α : Type u} {n : Nat} (b : PartialBlock α n) : PopResult α n :=
  b.rec .empty fun {n m} l r h ih =>
    ih.rec (fun _ => .shrink l.pop) (fun {m} r h => .done (.split l r h))
      (fun {m} r h => .done (.split l r (by simp_all; omega))) h

theorem FullBlock.toArray_pop {α : Type u} {n : Nat} (b : FullBlock α n) :
    b.pop.toArray = b.toVector.toArray.pop := by
  induction b with simp [toVector, PartialBlock.toArray, *]

theorem PartialBlock.pop_spec {α : Type u} {n : Nat} (b : PartialBlock α n) :
    match b.pop with
    | .empty => b.toArray = #[]
    | .done x => x.toArray = b.toArray.pop ∧ b.toArray ≠ #[]
    | .shrink x => x.toArray = b.toArray.pop ∧ b.toArray ≠ #[] := by
  induction b with
  | empty => simp [pop, toArray]
  | @split n m l r h ih =>
    simp only [Nat.succ_eq_add_one, pop]
    have (eq := a_eq) a := r.pop
    rw [← a_eq] at ih
    dsimp only [PartialBlock.pop] at a_eq
    rw [← a_eq]
    rcases a with _ | a | a <;> simp_all [FullBlock.toArray_pop, toArray]

theorem PartialBlock.pop_toArray_empty {α : Type u} :
    (toArray empty : Array α).pop = toArray empty := by simp [toArray]

theorem PartialBlock.pop_done {α : Type u} {n : Nat} {b b' : PartialBlock α n}
    (h : b.pop = .done b') : b.toArray.pop = b'.toArray := by
  have := pop_spec b
  simp_all

theorem PartialBlock.pop_shrink {α : Type u} {n : Nat} {b : PartialBlock α n.succ}
    {b' : PartialBlock α n} (h : b.pop = .shrink b') : b.toArray.pop = b'.toArray := by
  have := pop_spec b
  simp_all

theorem Nat.rec_eq {α zero succ n} :
    (Nat.rec zero succ n : α) =
      if n = 0 then zero else succ (n - 1) (Nat.rec zero succ (n - 1)) := by
  cases n <;> rfl

theorem FullBlock.get_eq {α : Type u} {n : Nat} {b : FullBlock α n} (i : Nat) :
    b.get i = b.toVector[i % 2 ^ n] := by
  induction b with
  | single => simp [Nat.mod_one, toVector]
  | @split n l r lih rih =>
    change (((i >>> n) % 2).rec (l.get i) (fun _ _ => r.get i) : α) = _
    simp only [lih, rih, Nat.succ_eq_add_one, toVector, Vector.getElem_cast]
    simp only [Nat.pow_succ, Nat.mod_mul, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ n) with h | h <;>
      simp [h, Nat.two_pow_pos, Nat.mod_lt, Nat.rec_eq]

theorem PartialBlock.getElem?_toArray {α : Type u} {n : Nat} {b : PartialBlock α n} {i : Nat} :
    b.toArray[i]? = b.get? i := by
  induction b generalizing i with
  | empty => simp [toArray]
  | @split n m l r h ih =>
    change _ = (((1 <<< n).ble i).rec (some (l.get i)) (r.get? (i - 1 <<< n)) : Option α)
    simp +contextual [Bool.rec_eq, Nat.shiftLeft_eq, toArray, Array.getElem?_append, ← Nat.not_lt,
      ih, FullBlock.get_eq, Nat.mod_eq_of_lt, ← dite_eq_ite]

theorem PartialBlock.getElem_toArray_of_eq_some {α : Type u} {n : Nat} {b : PartialBlock α n}
    {i : Nat} {x : α} (h : b.get? i = some x) (h' : i < b.toArray.size) : b.toArray[i]'h' = x := by
  rw [← Option.some_inj, ← h, ← getElem?_pos, getElem?_toArray]

theorem PartialBlock.getElem!_toArray_of_eq_some {α : Type u} [Inhabited α] {n : Nat}
    {b : PartialBlock α n} {i : Nat} {x : α} (h : b.get? i = some x) :
    b.toArray[i]! = x := by
  rw [← getElem?_toArray] at h
  rw [getElem!_def, h]

theorem FullBlock.toArray_modify {α : Type u} {n : Nat} {b : FullBlock α n} {i : Nat} {f : α → α} :
    (b.modify i f).toVector = b.toVector.set (i % 2 ^ n) (f b.toVector[i % 2 ^ n]) := by
  induction b with
  | single => simp [Nat.mod_one, toVector]
  | @split n l r lih rih =>
    change (((i >>> n) % 2).rec (.split (l.modify i f) r)
      (fun _ _ => .split l (r.modify i f)) : FullBlock α n.succ).toVector = _
    simp only [Nat.succ_eq_add_one, toVector, Vector.getElem_cast, ← Vector.toArray_inj,
      Vector.toArray_set, Vector.toArray_cast, Vector.toArray_append]
    simp only [Nat.pow_succ, Nat.shiftRight_eq_div_pow, Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ n) with h | h <;>
      simp [h, Nat.two_pow_pos, Nat.mod_lt, Array.set_append_left, toVector, lih, rih]

theorem PartialBlock.modify_toArray {α : Type u} {n : Nat} {b : PartialBlock α n}
    {i : Nat} {f : α → α} : b.toArray.modify i f = (b.modify f i).toArray := by
  simp only [← Array.toList_inj, Array.toList_modify]
  induction b generalizing i with
  | empty => simp [toArray]
  | @split n m l r h ih =>
    change _ = (((1 <<< n).ble i).rec (.split (l.modify i f) r h)
      (.split l (r.modify f (i - 1 <<< n)) h) : PartialBlock α n.succ).toArray.toList
    have : Inhabited α := ⟨l.get 0⟩
    simp +contextual [Bool.rec_eq, Nat.shiftLeft_eq, toArray, List.getElem?_append,
      List.modify_eq_set, ← dite_eq_ite, ← Nat.not_lt, apply_dite, FullBlock.toArray_modify,
      ← ih, Nat.mod_eq_of_lt]

theorem PartialBlock.setIfInBounds_toArray {α : Type u} {n : Nat} {b : PartialBlock α n}
    {i : Nat} {x : α} : b.toArray.setIfInBounds i x = (b.modify (fun _ => x) i).toArray := by
  ext j h h'
  · simp [← modify_toArray]
  · simp only [Array.size_setIfInBounds] at h
    simp [← modify_toArray, Array.getElem_modify, Array.getElem_setIfInBounds, h]

theorem PartialBlock.set_toArray {α : Type u} {n : Nat} {b : PartialBlock α n}
    {i : Nat} {x : α} (h : i < b.toArray.size) :
    b.toArray.set i x h = (b.modify (fun _ => x) i).toArray := by
  ext <;> simp [← modify_toArray, Array.getElem_modify, Array.getElem_set]

noncomputable def FullBlock.fill {α : Type u} (x : α) : (n : Nat) → FullBlock α n :=
  Nat.rec (.single x) fun _n ih => .split ih ih

noncomputable def natSize (n : Nat) : Nat :=
  n.rec .zero fun _ _ => n.log2.succ

theorem natSize_le_iff {a b : Nat} : natSize a ≤ b ↔ a < 2 ^ b := by
  simp only [natSize, Nat.succ_eq_add_one, Nat.rec_eq]
  split
  · simp [Nat.two_pow_pos, *]
  · simp [← Nat.log2_lt, Nat.add_one_le_iff, *]

inductive ReplicateResult (α : Type u) (n : Nat) where
  | mk (m : Nat) (h : m ≤ n) (x : PartialBlock α m)

noncomputable def PartialBlock.replicate {α : Type u} (x : α) :
    (n : Nat) → (m : Nat) → m.shiftRight n = 0 → ReplicateResult α n :=
  Nat.rec (fun _ _ => .mk .zero .refl .empty) fun n ih m hm =>
    if h : m.shiftRight n = 0 then
      ⟨(ih m h).1, (ih m h).2.step, (ih m h).3⟩
    else
      haveI := ih (m.sub ((nat_lit 1).shiftLeft n)) ?_
      .mk n.succ .refl (.split (.fill x n) this.3 (by simpa using this.2))
where finally
  simp_all [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.two_pow_succ, Nat.sub_lt_iff_lt_add]

theorem FullBlock.toVector_fill {α : Type u} (x : α) (n : Nat) :
    (fill x n).toVector = Vector.replicate (2 ^ n) x := by
  induction n with simp_all [fill, toVector, ← Vector.toArray_inj, Nat.two_pow_succ]

theorem PartialBlock.replicate_eq {α : Type u} (x : α) (n m : Nat)
    (h : m.shiftRight n = nat_lit 0) :
    Array.replicate m x = (PartialBlock.replicate x n m h).3.toArray := by
  induction n generalizing m with
  | zero =>
    have (motive zero succ : _) : @Nat.rec motive zero succ 0 = zero := rfl
    simp only [replicate]
    rw [this]
    simpa [toArray, Nat.rec_eq, this] using h
  | succ k ih =>
    simp only [replicate]
    have (eq := f_eq) f := PartialBlock.replicate x k
    rw [← f_eq] at ih
    dsimp only [PartialBlock.replicate] at f_eq
    rw [← f_eq]
    by_cases h' : m.shiftRight k = 0
    · rw [dite_eq_left h']
      simp [← ih]
    · rw [dite_eq_right h']
      simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff,
        Nat.pow_eq_zero, reduceCtorEq, ne_eq, false_and, false_or, Nat.not_lt] at h'
      simp [toArray, FullBlock.toVector_fill, ← ih, Nat.shiftLeft_eq, h']

noncomputable def PartialBlock.size {α : Type u} {n : Nat} : PartialBlock α n → Nat :=
  PartialBlock.rec (nat_lit 0) fun {n _m} _l _r _h => Nat.add (Nat.shiftLeft (nat_lit 1) n)

theorem PartialBlock.size_toArray {α : Type u} {n : Nat} (x : PartialBlock α n) :
    x.toArray.size = x.size := by
  induction x with simp [toArray, size, *, Nat.shiftLeft_eq]

noncomputable abbrev FullBlock.map {α : Type u} {β : Type v} (f : α → β) :
    {n : Nat} → (x : FullBlock α n) → FullBlock β n :=
  FullBlock.rec (fun x => .single (f x)) (fun {_n} _l _r => FullBlock.split)

noncomputable def PartialBlock.map {α : Type u} {β : Type v} (f : α → β) :
    {n : Nat} → (x : PartialBlock α n) → PartialBlock β n :=
  PartialBlock.rec .empty (fun {_n _m} l _r h ih => PartialBlock.split (l.map f) ih h)

theorem FullBlock.toVector_map {α : Type u} {β : Type v} {n : Nat} (x : FullBlock α n)
    (f : α → β) : (x.map f).toVector = x.toVector.map f := by
  induction x with simp [toVector, ← Vector.toArray_inj, *]

theorem PartialBlock.map_toArray {α : Type u} {β : Type v} {n : Nat} (x : PartialBlock α n)
    (f : α → β) : x.toArray.map f = (x.map f).toArray := by
  induction x with simp [toArray, map, FullBlock.toVector_map, *]

attribute [cbv_opaque] Array.emptyWithCapacity Array.getInternal Array.get!Internal
  Array.push Array.pop Array.modify Array.setIfInBounds Array.set Array.replicate Array.size
  Array.map

end Lean.Sym
