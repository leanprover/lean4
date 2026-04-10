/-!
# Preparations
-/

/-!
## General GetElemV
-/

class GetElemV (coll : Type u) (idx : Type v) (elem : outParam (Type w)) where
  getElemV [h : Nonempty elem] (xs : coll) (i : idx) : elem

export GetElemV (getElemV)

@[inherit_doc getElem]
syntax:max term noWs "｢" withoutPosition(term) "｣" : term
macro_rules | `($x｢$i｣) => `(getElemV $x $i (h := by first | assumption | infer_instance | exact ⟨by assumption⟩ | exact ⟨$x[$i]⟩))

class LawfulGetElemV (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop))
    [GetElem? cont idx elem dom] [GetElemV cont idx elem] : Prop where
  getElemV_def {_ : Nonempty elem} (c : cont) (i : idx) :
    c｢i｣ = match c[i]? with | some e => e | none => Classical.ofNonempty

export LawfulGetElemV (getElemV_def)

@[simp, grind norm]
theorem getElem_eq_getElemV [GetElem? cont idx elem dom]
    [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) :
    c[i] = c｢i｣ := by
  simp [getElemV_def, getElem?_pos, h]

attribute [- simp, - grind] getElem?_pos
attribute [- simp] some_getElem_eq_getElem?_iff

@[grind =, simp]
theorem getElem?_eq_some_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) :
    c[i]? = some c｢i｣ := by
  have : Decidable (dom c i) := .isTrue h
  simp only [getElem?_def, getElem_eq_getElemV]
  exact dif_pos h

theorem getElemV_pos [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) :
    c｢i｣ = c[i]'h := by
  rw [getElemV_def, getElem?_pos]

theorem getElemV_neg [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {_ : Nonempty elem}
    (c : cont) (i : idx) (h : ¬dom c i) :
    c｢i｣ = Classical.ofNonempty := by
  rw [getElemV_def, getElem?_neg _ _ h]

@[simp]
theorem some_getElemV_eq_getElem?_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] (h : dom c i) :
    (some c｢i｣ = c[i]?) ↔ True := by
  simp [h]

attribute [- simp] getElem?_eq_some_getElem_iff

@[simp] theorem getElem?_eq_some_getElemV_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] (h : dom c i) :
    haveI : Nonempty elem := ⟨c[i]⟩
    (c[i]? = some c｢i｣) ↔ True := by
  simp [h]

theorem getElem?_eq_some_iff_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] {a : elem} :
    c[i]? = some a ↔ dom c i ∧ c｢i｣ = a := by
  simp only [getElem?_eq_some_iff]
  simpa [getElem_eq_getElemV] using ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

/-!
## GetElemV for lists
-/

namespace List

noncomputable def getElemVInternal [Nonempty α] : (as : List α) → (i : Nat) → α
  | a::_,  0   => a
  | _::as, n+1 => getElemVInternal as n
  | _,     _   => Classical.ofNonempty

noncomputable instance : GetElemV (List α) Nat α where
  getElemV xs i := xs.getElemVInternal i

instance : LawfulGetElemV (List α) Nat α fun as i => i < as.length where
  getElemV_def as i := by
    simp only [getElemV, getElem?]
    induction as generalizing i with
    | nil => rfl
    | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

noncomputable def headV [Nonempty α] (l : List α) : α :=
  l.head?.getD Classical.ofNonempty

noncomputable def getLastV [Nonempty α] (l : List α) : α :=
  l.getLast?.getD Classical.ofNonempty

@[simp, grind norm]
theorem head_eq_headV {l : List α} (h : l ≠ []) : haveI : Nonempty α := ⟨l.head h⟩; l.head h = l.headV := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => unfold headV; simp

@[simp, grind norm]
theorem getLast_eq_getLastV {l : List α} (h : l ≠ []) :
    haveI : Nonempty α := ⟨l.getLast h⟩; l.getLast h = l.getLastV := by
  unfold getLastV
  rw [getLast?_eq_some_getLast h]
  rfl

attribute [- simp] getElem_mem

@[simp]
theorem getElemV_mem {l : List α} {n} (h : n < l.length) : l｢n｣ ∈ l :=
  match l, n with
  | _ :: _, 0 => .head ..
  | _ :: l, _+1 => .tail _ (getElemV_mem (l := l) (by simpa [Nat.add_one_lt_add_one_iff] using h) ..)

grind_pattern getElemV_mem => l｢n｣ ∈ l

attribute [- simp] getElem_cons_zero

@[simp] theorem getElemV_cons_zero {l : List α} :
    haveI : Nonempty α := ⟨a⟩
    (a::l)｢0｣ = a :=
  rfl

attribute [- simp] getElem_cons_succ

@[simp] theorem getElemV_cons_succ {l : List α} :
    haveI : Nonempty α := ⟨a⟩
    (a::l)｢i+1｣ = l｢i｣ :=
  rfl

attribute [- simp] getElem_cons_drop

@[simp]
theorem getElemV_cons_drop {as : List α} {i : Nat} {_ : Nonempty α} (h : i < as.length) :
    as｢i｣ :: as.drop (i+1) = as.drop i := by
  simp [getElemV_pos as i h, getElem_cons_drop, - getElem_eq_getElemV]

theorem getElem?_eq_getElemV {l : List α} {i} (h : i < l.length) :
    haveI : Nonempty α := ⟨l[i]⟩
    l[i]? = some l｢i｣ := by
  induction l generalizing i with
  | nil => cases h
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.getElem?_eq_getElem h]

attribute [- simp] getElem_append_left

@[simp]
theorem getElemV_append_left {as bs : List α} (h : i < as.length) :
    haveI : Nonempty α := ⟨as[i]⟩
    (as ++ bs)｢i｣ = as｢i｣ := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i =>
      apply ih
      simpa [Nat.add_one_lt_add_one_iff] using h

attribute [- simp] getElem_append_right

@[simp]
theorem getElemV_append_right {_ : Nonempty α} {as bs : List α} {i : Nat} (h₁ : as.length ≤ i) :
    (as ++ bs)｢i｣ =
      bs｢i - as.length｣ := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    cases i with simp [Nat.succ_sub_succ] <;> simp at h₁
    | succ i => apply ih; simp [h₁]

attribute [- grind] getElem_append

@[grind =] theorem getElemV_append {_ : Nonempty α} {l₁ l₂ : List α} {i : Nat} :
    (l₁ ++ l₂)｢i｣ = if i < l₁.length then l₁｢i｣ else l₂｢i - l₁.length｣ := by
  split <;> rename_i h
  · exact getElemV_append_left h
  · exact getElemV_append_right (by simpa using h)

attribute [- simp, - grind] getElem_map

@[simp, grind =] theorem getElemV_map (f : α → β) {l : List α} {i : Nat} (h : i < l.length) :
    haveI : Nonempty β := ⟨f l[i]⟩
    (map f l)｢i｣ = f l｢i｣ := by
  have := getElem_map f (l := l) (i := i) (h := by simpa using h)
  simpa using this

attribute [- grind] head_eq_getElem

@[grind =]
theorem headV_eq_getElemV {_ : Nonempty α} {l : List α} : headV l = l｢0｣ := by
  cases l <;> rfl

attribute [- grind] getElem_insert

@[grind =] theorem getElemV_insert [BEq α] [LawfulBEq α] {l : List α} {a : α} {i : Nat} :
    (l.insert a)｢i｣ = if a ∈ l then l｢i｣ else if i = 0 then a else l｢i - 1｣ := by
  rw [getElemV_def, getElem?_insert]
  by_cases a ∈ l
  · simp [*, getElemV_def]
  · match i with
    | 0 => simp [*]
    | i' + 1 => simp [*, getElemV_def]

set_option warn.sorry false in
protected theorem minIdxOn_le_of_apply_getElemV_le_apply_minOn {_ : Nonempty α} [LE β]
    [DecidableLE β] [Std.IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ [])
    {k : Nat} (hle : f xs｢k｣ ≤ f (xs.minOn f h)) :
    xs.minIdxOn f h ≤ k := by
  sorry -- uses private lemmas

theorem getElemV_of_mem {l : List α} (h : a ∈ l) :
    ∃ (i : Nat), i < l.length ∧ l｢i｣ = a :=
  match l, h with
  | _ :: _, .head .. => ⟨0, Nat.succ_pos _, rfl⟩
  | _ :: _, .tail _ m => let ⟨i, h, e⟩ := getElemV_of_mem m; ⟨i+1, Nat.succ_lt_succ h, e⟩

theorem mem_iff_getElemV {a} {xs : List α} : a ∈ xs ↔ ∃ (i : Nat), i < xs.length ∧ xs｢i｣ = a :=
  ⟨getElemV_of_mem, fun ⟨_, _, e⟩ => e ▸ getElemV_mem ‹_› ..⟩

attribute [- simp, - grind] head_append_of_ne_nil

@[simp, grind =]
theorem headV_append_of_ne_nil {l : List α} (h : l ≠ []) :
    haveI : Nonempty α := ⟨l.head h⟩
    (l ++ l').headV = l.headV := by
  match l with
  | a :: l => rfl

attribute [- grind] head_append

@[grind =]
theorem headV_append {_ : Nonempty α} {l₁ l₂ : List α} :
    (l₁ ++ l₂).headV = if l₁.isEmpty then l₂.headV else l₁.headV := by
  split <;> rename_i h
  · simp only [isEmpty_iff] at h
    subst h
    simp
  · simp only [isEmpty_iff] at h
    simp [h]

@[simp] theorem getLastV_mem {l : List α} (h : l ≠ []) :
    haveI : Nonempty α := ⟨l.head h⟩
    l.getLastV ∈ l :=
  match l with
  | [] => absurd rfl h
  | [_] => .head ..
  | _::a::l => .tail _ <| getLastV_mem (cons_ne_nil a l)

end List

/-!
## GetElemV for arrays
-/

namespace Array

noncomputable instance : GetElemV (Array α) Nat α where
  getElemV xs i := xs.getD i Classical.ofNonempty

instance : LawfulGetElemV (Array α) Nat α fun xs i => i < xs.size where
  getElemV_def xs i := by
    simp only [getElemV, getElem?, decidableGetElem?, getD, getElem]
    split <;> rfl

attribute [- simp] getInternal_eq_getElem

@[simp]
theorem getInternal_eq_getElemV (a : Array α) (i : Nat) (h) :
    haveI : Nonempty α := ⟨a.getInternal i h⟩
    a.getInternal i h = a｢i｣ := by
  simp [getElemV_pos a i h, getInternal_eq_getElem, - getElem_eq_getElemV]

theorem getElemV_shrink {xs : Array α} {i j : Nat}
    (h : j < (xs.shrink i).size) :
    haveI : Nonempty α := ⟨(xs.shrink i)[j]⟩
    (xs.shrink i)｢j｣ = xs｢j｣ := by
  rwa [← getElem_eq_getElemV, getElem_shrink, getElem_eq_getElemV]

attribute [- simp, - grind] getElem_extract

/--
`getElem_extract` has a `(h : i < (xs.extract start stop).size)` hypothesis, but this is
unnecessarily strong for `getElemV_extract`.
-/
@[simp, grind =] theorem getElemV_extract {_ : Nonempty α} {xs : Array α} {start stop : Nat}
    (h : start + i < stop) :
    (xs.extract start stop)｢i｣ = xs｢start + i｣ := by
  by_cases start + i < xs.size
  · rw [← getElem_eq_getElemV, ← getElem_eq_getElemV, getElem_extract]
    simp; omega
  · rw [getElemV_neg, getElemV_neg]
    · simp; omega
    · simp; omega

theorem ext_getElemV {xs ys : Array α}
    (h₁ : xs.size = ys.size)
    (h₂ : (i : Nat) → (hi : i < xs.size) → haveI : Nonempty α := ⟨xs[i]⟩; xs｢i｣ = ys｢i｣)
    : xs = ys := by
  apply ext
  case h₁ => assumption
  case h₂ => simp +contextual [*]

attribute [- simp, - grind] getElem_toList

@[simp, grind =] theorem getElemV_toList {_ : Nonempty α} {xs : Array α} {i : Nat} : xs.toList｢i｣ = xs｢i｣ := by
  simp [getElemV_def, getElem?_toList]

attribute [- simp, - grind] _root_.List.getElem_toArray

@[simp, grind =] theorem _root_.List.getElemV_toArray [Nonempty α] {xs : List α} {i : Nat} :
    xs.toArray｢i｣ = xs｢i｣ := by
  simp [getElemV_def, _root_.List.getElem?_toArray]

attribute [- simp] getElem_append_left

@[simp] theorem getElemV_append_left {xs ys : Array α} {i : Nat} (hlt : i < xs.size) :
    haveI : Nonempty α := ⟨xs[i]⟩; (xs ++ ys)｢i｣ = xs｢i｣ := by
  simp only [← getElemV_toList, toList_append]
  rw [List.getElemV_append_left]
  simpa

theorem getElemV_push_lt {xs : Array α} {x : α} {i : Nat} (h : i < xs.size) :
    (xs.push x)｢i｣ = xs｢i｣ := by
  rw [Array.size] at h
  simp only [push, ← getElemV_toList, List.concat_eq_append, List.getElemV_append_left h]

attribute [- simp] getElem_push_eq

@[simp] theorem getElemV_push_eq {xs : Array α} {x : α} :
    (xs.push x)｢xs.size｣ = x := by
  simp only [push, ← getElemV_toList, List.concat_eq_append]
  rw [List.getElemV_append_right] <;> simp

attribute [- grind] getElem_push

@[grind =] theorem getElemV_push {xs : Array α} {x : α} {i : Nat} (h : i ≤ xs.size) :
    (xs.push x)｢i｣ = if i < xs.size then xs｢i｣ else x := by
  by_cases h' : i < xs.size
  · simp [getElemV_push_lt, h']
  · simp [Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_succ_of_le h)) (Nat.ge_of_not_lt h')]

attribute [- grind] getElem_append

@[grind =] theorem getElemV_append {_ : Nonempty α} {xs ys : Array α} {i : Nat} :
    (xs ++ ys)｢i｣ = if i < xs.size then xs｢i｣ else ys｢i - xs.size｣ := by
  cases xs; cases ys
  simp [List.getElemV_append]

attribute [- simp] getElem_ofFn

@[simp] theorem getElemV_ofFn {f : Fin n → α} {i : Nat} (h : i < n) :
    haveI : Nonempty α := ⟨f ⟨i, h⟩⟩
    (ofFn f)｢i｣ = f ⟨i, h⟩ := by
  rw [← getElem_eq_getElemV, getElem_ofFn]
  simpa

attribute [- simp, - grind] getElem_finRange

@[simp, grind =] theorem getElemV_finRange {i : Nat} (h : i < n) :
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    (Array.finRange n)｢i｣ = Fin.cast size_finRange ⟨i, by simpa using h⟩ := by
  simp [Array.finRange, getElemV_ofFn h]

attribute [- simp, - grind] getElem_map

@[simp, grind =] theorem getElemV_map (f : α → β) {xs : Array α} {i : Nat}
    (hi : i < xs.size) :
    haveI : Nonempty α := ⟨xs[i]⟩
    haveI : Nonempty β := ⟨f xs[i]⟩
    (xs.map f)｢i｣ = f xs｢i｣ := by
  cases xs
  simp [List.getElemV_map _ (by simpa using hi)]

end Array

/-!
# Tests
-/

/-!
## `simp` lemmas becoming less automatic
-/

namespace Array

/--
Original proof:
```lean
  apply List.ext_getElem
  · simp
  · intro i; cases i <;> simp
```
The new proof is much more manual.
-/
theorem finRange_succ_copy {n} : Array.finRange (n+1) = #[0] ++ (Array.finRange n).map Fin.succ := by
  ext i h₁ h₂
  · simp [Nat.add_comm]
  · simp [getElemV_append]
    split
    · rw [getElemV_finRange] <;> simp [*]
    · rw [getElemV_finRange, getElemV_map, getElemV_finRange]
      · simp only [Fin.cast_mk, Fin.succ_mk]; omega
      · have : 1 ≤ i := by omega
        simpa [Nat.sub_lt_iff_lt_add, *] using h₁
      · have : 1 ≤ i := by omega
        simpa [Nat.sub_lt_iff_lt_add, *] using h₁
      · simpa using h₁

attribute [- grind] getElem?_push

/--
The old proof was just:
```lean
simp [getElem?_def, getElem_push]
(repeat' split) <;> first | rfl | omega
```

The complication: The `simp` now needs to use `getElemV_push`, and the side condition needs `omega`.
We can't simply use `rw` before the `split` because the rewrite target is under a binder.

As an alternative, the old proof pattern would work if we used `(discharger := omega)`.
-/
@[grind =]
theorem getElem?_push_copy {xs : Array α} {x} : (xs.push x)[i]? = if i = xs.size then some x else xs[i]? := by
  simp only [getElem?_def, size_push, getElem_eq_getElemV]
  split
  · rw [getElemV_push (by omega)]
    (repeat' split) <;> first | rfl | omega
  · (repeat' split) <;> first | rfl | omega

attribute [- simp] shrink_eq_take

-- Previously, the proof was just `ext <;> simp [size_shrink, getElem_shrink]`.,
@[simp] theorem shrink_eq_take_copy {xs : Array α} {i : Nat} : xs.shrink i = xs.take i := by
  apply ext_getElemV -- we'll make this the default for `ext` in the future
  · simp [size_shrink]
  · intro i h
    -- We use `rw` here because `getElemV_extract` has a nontrivial side condition.
    rw [take_eq_extract, getElemV_shrink h, getElemV_extract, Nat.zero_add]
    simp [size_shrink] at *; omega -- side condition for `getElemV_extract`

attribute [- simp] extract_extract

/-
@[simp] theorem extract_extract {as : Array α} {i j k l : Nat} :
    (as.extract i j).extract k l = as.extract (i + k) (min (i + l) j) := by
  ext m h₁ h₂
  · simp
    omega
  · simp only [size_extract] at h₁ h₂
    simp [Nat.add_assoc]
-/

theorem extract_extract_copy {as : Array α} {i j k l : Nat} :
    (as.extract i j).extract k l = as.extract (i + k) (min (i + l) j) := by
  ext m h₁ h₂
  · simp
    omega
  · /-
    This block was:
    ```lean
    simp only [size_extract] at h₁ h₂
    simp [Nat.add_assoc]
    ```
    Now we need bounds proofs for `getElemV_extract`.
    -/
    simp only [getElem_eq_getElemV]
    rw [getElemV_extract, getElemV_extract, getElemV_extract (by simp at h₂; omega), Nat.add_assoc]
    · simp only [size_extract] at h₁ ⊢
      omega
    · simp only [size_extract] at h₁ ⊢
      omega

end Array

/-!
## Rewrite-in-proof anomaly
-/

set_option warn.sorry false in
example (xs : List α) (h : xs.length ≤ i) (hj : xs.length ≤ j) (hk : k < xs.length) :
    haveI : Nonempty α := ⟨(xs.set j xs｢k｣)[k]'(by simpa using hk)⟩
    xs｢i｣ = xs｢j｣ := by
  -- The second rewrite happens inside the `Nonempty` instance of `ofNonempty`.
  -- Expected: The second rewrite applies to the RHS.
  rw [getElemV_neg, getElemV_neg]
  · sorry
  · sorry
  · sorry

/-!
## Spurious dependencies
-/

namespace List

theorem headV_insert [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    haveI : Nonempty α := ⟨a⟩
    (l.insert a).headV = if a ∈ l then l.headV else a := by
  simp [headV_eq_getElemV, getElemV_insert]

theorem head_insert_copy [BEq α] [LawfulBEq α] {l : List α} {a : α} (w) :
    (l.insert a).head w = if h : a ∈ l then l.head (ne_nil_of_mem h) else a := by
  -- RHS has a spurious dependency, preventing it to be rewritten to `ite`
  simp [headV_insert, ← dite_eq_ite]

theorem lex_eq_true_iff_exists_getElemV [Nonempty α] [BEq α] {lt : α → α → Bool}
    {l₁ l₂ : List α} :
    lex l₁ l₂ lt = true ↔
      (l₁.isEqv (l₂.take l₁.length) (· == ·) ∧ l₁.length < l₂.length) ∨
        (∃ (i : Nat), i < l₁.length ∧ i < l₂.length ∧
          (∀ j, j < i → l₁｢j｣ == l₂｢j｣) ∧ lt l₁｢i｣ l₂｢i｣) := by
  -- The given proof has a spurious dependency on the `i < ...` bounds proofs.
  simpa [← exists_prop] using lex_eq_true_iff_exists (l₁ := l₁) (l₂ := l₂) lt

protected theorem minIdxOn_le_of_apply_getElemV_le_apply_getElemV [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} (hi : i < xs.length)
    (hi' : ∀ j, (_ : j < xs.length) → f xs｢i｣ ≤ f xs｢j｣) :
    xs.minIdxOn f h ≤ i := by
  apply List.minIdxOn_le_of_apply_getElemV_le_apply_minOn h
  simp only [List.le_apply_minOn_iff, List.mem_iff_getElemV]
  /-
  The old proof used `rfl` place of `h : getElem xs j = x`.
  This doesn't work anymore because the `Nonempty` instance used by `getElemV` is `⟨x⟩`
  -> occurs check fails, `cases h` fails.

  The new proof uses `▸` and isn't less convenient, but the error message is a bad user experience.
  -/
  rintro _ ⟨j, hj, h⟩
  exact h ▸ hi' _ hj

theorem prefix_iff_getElemV [Nonempty α] {l₁ l₂ : List α} :
    l₁ <+: l₂ ↔ ∃ (_ : l₁.length ≤ l₂.length),
      ∀ i, i < l₁.length → l₁｢i｣ = l₂｢i｣ := by
  -- Have to disable `exists_prop` because the LHS has a spurious dependency on `l₁.length ≤ l₂.length`.
  simp [prefix_iff_getElem, - exists_prop]

theorem isEqv_eq_decide_getElemV {_ : Nonempty α} {as bs : List α} {r : α → α → Bool} :
    isEqv as bs r = if as.length = bs.length then
      decide (∀ (i : Nat), i < as.length → r as｢i｣ bs｢i｣) else false := by
  -- Have to disable `Bool.if_false_right` because of spurious dependency
  simpa [- Bool.if_false_right] using isEqv_eq_decide (as := as) (bs := bs) (r := r)

theorem head_append_copy {l₁ l₂ : List α} (w : l₁ ++ l₂ ≠ []) :
    head (l₁ ++ l₂) w =
      if h : l₁.isEmpty then
        head l₂ (by simp_all [isEmpty_iff])
      else
        head l₁ (by simp_all [isEmpty_iff]) := by
  -- `dite_eq_ite` doesn't trigger because of spurious dependency,
  -- so we must apply it in reverse to assimilate LHS and RHS
  simp [headV_append, ← dite_eq_ite]

end List
