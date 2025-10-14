module
import all Lean.Compiler.NameMangling
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.Nat.Basic

/-!
# Test behavior of name mangling
-/

def checkMangle (n : Lean.Name) (s : String) : IO Unit := do
  if n.mangle "" ≠ s then
    throw <| .userError s!"failed: {n} mangles to {n.mangle ""} but expected {s}"
  if .unmangle s ≠ n then
    throw <| .userError s!"failed: {s} unmangles to {Lean.Name.unmangle s} but expected {n}"

/-!
Mangling simple identifiers with optional number components and preceding underscores.
-/

#eval checkMangle `ab12 "ab12"
#eval checkMangle ``Lean.Name.mangle "Lean_Name_mangle"
#eval checkMangle `Lean.Name.mangle._aux "Lean_Name_mangle___aux"
#eval checkMangle ((`_private.Lean.Compiler.NameMangling).num 0 ++ `Lean.Name.mangleAux)
    "__private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux"

/-!
Escape sequences in mangled identifiers.
-/

#eval checkMangle `«ÿ» "00_xff"
#eval checkMangle `«α₁» "00_u03b1_u2081"
#eval checkMangle `«𝒫» "00_U0001d4ab"

/-!
Escape sequence disambiguation
-/

#eval checkMangle `a' "a_x27"
#eval checkMangle `a.x27 "a_00x27"
#eval checkMangle `a_' "a___x27"
#eval checkMangle `a._x27 "a_00__x27"
#eval checkMangle `a.u0027 "a_00u0027"
#eval checkMangle `a.U00000027 "a_00U00000027"
#eval checkMangle `a.ucafe "a_00ucafe"
#eval checkMangle `a.uCAFE "a_uCAFE" -- uppercase does not need to be disambiguated

/-!
Trailing underscores in names
-/

#eval checkMangle `a._b "a___b"
#eval checkMangle `a_.b "a___00b"
#eval checkMangle `a_ "a__"
#eval checkMangle `a_.«» "a___00"
#eval checkMangle `a.__ "a_00____"

/-!
Empty name components
-/

#eval checkMangle `a_b "a__b"
#eval checkMangle `a.«».b "a_00_b"
#eval checkMangle `«».b "00_b"
#eval checkMangle `b_.«» "b___00"

/-!
Numbers vs numbers in text
-/

#eval checkMangle ((`a).num 2 ++ `b) "a_2__b"
#eval checkMangle `a.«2_b» "a_002__b"

/-!
Consecutive number components
-/

#eval checkMangle ((`a).num 2 |>.num 3 |>.str "" |>.num 4) "a_2__3__00_4_"

/-!
Preceding number components
-/

#eval checkMangle (.str (.num .anonymous 4) "hi") "4__hi"

/-!
Anonymous vs empty string
-/

#eval checkMangle .anonymous ""
#eval checkMangle `«» "00"
#eval checkMangle `«».«» "00_00"

@[simp]
theorem String.push_ne_empty : String.push s c ≠ "" := by
  simp [← String.bytes_inj]

@[simp]
theorem String.singleton_ne_empty : String.singleton c ≠ "" := by
  simp [← String.bytes_inj]

@[simp]
theorem String.append_right_inj {t₁ t₂ : String} (s : String) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ := by
  simp [ByteArray.append_right_inj, ← String.bytes_inj]

def String.posBetween (s t : String) : (s ++ t).ValidPos :=
  ⟨s.endPos, by simp [Pos.Raw.isValid_append]⟩

@[simp]
theorem String.posBetween_eq_endValidPos_iff (s t : String) :
    @Eq (no_index _) (s.posBetween t) (String.endValidPos (no_index _)) ↔ t = "" := by
  simp [String.ValidPos.ext_iff, String.Pos.Raw.ext_iff, String.posBetween]

@[simp]
theorem String.posBetween_eq_startValidPos_iff (s t : String) :
    @Eq (no_index _) (s.posBetween t) (String.startValidPos (no_index _)) ↔ s = "" := by
  simp [String.ValidPos.ext_iff, String.Pos.Raw.ext_iff, String.posBetween]

@[simp]
theorem String.length_eq_zero_iff {s : String} : s.length = 0 ↔ s = "" := by
  simp [← String.length_data]

@[simp]
theorem String.append_eq_empty_iff {s t : String} : s ++ t = "" ↔ s = "" ∧ t = "" := by
  simp [← String.bytes_inj]

@[simp]
theorem String.get_posBetween_singleton_append {s t : String} {c : Char} (h) :
    (s.posBetween (String.singleton c ++ t)).get h = c := by
  simp only [ValidPos.get, Slice.Pos.get, str_toSlice, startInclusive_toSlice, offset_startValidPos,
    Pos.Raw.byteIdx_zero, posBetween, ValidPos.offset_toSlice, byteIdx_endPos, Nat.zero_add]
  simp only [decodeChar, bytes_append, bytes_singleton, ByteArray.utf8DecodeChar]
  rw [← Option.some.injEq, Option.some_get, ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract]
  rw [← String.size_bytes, ByteArray.extract_append_eq_right rfl (by simp)]
  rw [List.utf8DecodeChar?_utf8Encode_singleton_append]

@[simp]
theorem String.next_posBetween_singleton_append {s t : String} {c : Char} (h) :
    (s.posBetween (String.singleton c ++ t)).next h =
      ((s.push c).posBetween t).cast (by simp only [String.push_eq_append, String.append_assoc]) := by
  simp only [ValidPos.next, ValidPos.ext_iff, Slice.Pos.ofset_ofSlice, ValidPos.offset_cast,
    Pos.Raw.ext_iff, Slice.Pos.byteIdx_offset_next, ValidPos.offset_toSlice]
  rw [← String.ValidPos.get.eq_def _ h, String.get_posBetween_singleton_append]
  simp [String.posBetween]

theorem ByteArray.utf8ByteSize_of_parseFirstByte (b : UInt8) (h : b.IsUTF8FirstByte) :
    b.utf8ByteSize h =
      match ByteArray.utf8DecodeChar?.parseFirstByte b with
      | .done => ⟨1⟩
      | .oneMore => ⟨2⟩
      | .twoMore => ⟨3⟩
      | .threeMore | .invalid => ⟨4⟩ := by
  rw [UInt8.utf8ByteSize, utf8DecodeChar?.parseFirstByte]
  simp only [beq_iff_eq]
  split; rfl; split; rfl; split; rfl
  by_cases hb : b &&& 248 = 240 <;> simp [hb]

theorem ByteArray.isInvalidContinuationByte_of_isUTF8FirstByte {b : UInt8}
    (h : UInt8.IsUTF8FirstByte b) : utf8DecodeChar?.isInvalidContinuationByte b := by
  rcases b with ⟨a⟩
  decide +revert

theorem ByteArray.add_lt_size_of_isSome_utf8DecodeChar? {b : ByteArray} {i : Nat} {k : Nat}
    (h : (b.utf8DecodeChar? i).isSome)
    (hkb : k < ((b[i]'(lt_size_of_isSome_utf8DecodeChar? h)).utf8ByteSize
      (isUTF8FirstByte_of_isSome_utf8DecodeChar? h)).byteIdx) :
    i + k < b.size := by
  have hbi := lt_size_of_isSome_utf8DecodeChar? h
  have hfb : b[i].IsUTF8FirstByte := isUTF8FirstByte_of_isSome_utf8DecodeChar? h
  change k < ((b[i]'hbi).utf8ByteSize hfb).byteIdx at hkb
  revert h
  fun_cases utf8DecodeChar? with
  | case1 | case4 | case6 | case8 | case9 => nofun
  | case2 =>
    rename_i hfb
    simp only [utf8ByteSize_of_parseFirstByte, hfb, Nat.lt_one_iff] at hkb
    simp [hkb, hbi]
  | case3 | case5 | case7 =>
    rename_i hfb hi
    simp only [utf8ByteSize_of_parseFirstByte, hfb] at hkb
    intro; omega

theorem ByteArray.isInvalidContinuationByte_of_isSome_utf8DecodeChar? {b : ByteArray} {i : Nat} {k : Nat}
    (h : (b.utf8DecodeChar? i).isSome) (hk : 0 < k)
    (hkb : k < ((b[i]'(lt_size_of_isSome_utf8DecodeChar? h)).utf8ByteSize
      (isUTF8FirstByte_of_isSome_utf8DecodeChar? h)).byteIdx) :
    utf8DecodeChar?.isInvalidContinuationByte
      (b[i + k]'(add_lt_size_of_isSome_utf8DecodeChar? h hkb)) = false := by
  have hbi := lt_size_of_isSome_utf8DecodeChar? h
  have hfb : b[i].IsUTF8FirstByte := isUTF8FirstByte_of_isSome_utf8DecodeChar? h
  have hbik := add_lt_size_of_isSome_utf8DecodeChar? h hkb
  change k < ((b[i]'hbi).utf8ByteSize hfb).byteIdx at hkb
  change utf8DecodeChar?.isInvalidContinuationByte b[i + k] = false
  revert h
  fun_cases utf8DecodeChar? with
  | case1 | case4 | case6 | case8 | case9 => nofun
  | case2 =>
    rename_i hfb
    simp only [utf8ByteSize_of_parseFirstByte, hfb, Nat.lt_one_iff] at hkb
    cases hkb; cases hk
  | case3 =>
    rename_i hfb _
    simp only [utf8ByteSize_of_parseFirstByte, hfb] at hkb
    cases show k = 1 by omega
    simp [utf8DecodeChar?.assemble₂, apply_ite Option.isSome, imp.swap]
  | case5 =>
    rename_i hfb _
    simp only [utf8ByteSize_of_parseFirstByte, hfb] at hkb
    obtain rfl | rfl := (show k = 1 ∨ k = 2 by omega) <;>
      simp +contextual [utf8DecodeChar?.assemble₃, apply_ite Option.isSome]
  | case7 =>
    rename_i hfb _
    simp only [utf8ByteSize_of_parseFirstByte, hfb] at hkb
    obtain rfl | rfl | rfl := (show k = 1 ∨ k = 2 ∨ k = 3 by omega) <;>
      simp +contextual [utf8DecodeChar?.assemble₄, apply_ite Option.isSome]

theorem ByteArray.not_isUTF8FirstByte_of_isSome_utf8DecodeChar? {b : ByteArray} {i : Nat} {k : Nat}
    (h : (b.utf8DecodeChar? i).isSome) (hk : 0 < k)
    (hkb : k < ((b[i]'(lt_size_of_isSome_utf8DecodeChar? h)).utf8ByteSize
      (isUTF8FirstByte_of_isSome_utf8DecodeChar? h)).byteIdx) :
    ¬ (b[i + k]'(add_lt_size_of_isSome_utf8DecodeChar? h hkb)).IsUTF8FirstByte :=
  have := isInvalidContinuationByte_of_isSome_utf8DecodeChar? h hk hkb
  mt isInvalidContinuationByte_of_isUTF8FirstByte ((Bool.not_eq_true _).mpr this)

theorem String.Slice.findNextPos.go_eq_next_of_le_of_lt {s : Slice} {p : s.Pos} {p' : Pos.Raw} {h}
    (h₁ : p.offset < p') (h₂ : p' ≤ (p.next h).offset) :
    findNextPos.go s p' = p.next h := by
  ext
  rw [findNextPos.go]
  split
  · rename_i h'
    have hp := p.isValidForSlice
    rw [Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar?] at hp
    have hplt := Nat.lt_trans h₁ h'
    simp only [Pos.Raw.ext_iff, Nat.ne_of_lt hplt, false_or] at hp
    have hp' (k : Nat) := ByteArray.not_isUTF8FirstByte_of_isSome_utf8DecodeChar? (k := k) hp.2
    by_cases hp'eq : p' = (p.next h).offset
    · simp only [hp'eq]
      rw [dif_pos]
      · rfl
      · rw [hp'eq] at h'
        have hne : p.next h ≠ s.endPos := by intro; simp_all
        exact (p.next h).isUTF8FirstByte_byte (h := hne)
    · replace h₂ := Nat.lt_of_le_of_ne h₂ (mt String.Pos.Raw.ext hp'eq)
      rw [dif_neg]
      · have : p'.byteIdx < p'.inc.byteIdx := @Nat.lt_add_of_pos_right 1 p'.byteIdx (by decide)
        have : p'.inc.byteIdx ≤ s.utf8ByteSize.byteIdx := h'
        rw [go_eq_next_of_le_of_lt]
        · exact Nat.lt_add_right 1 h₁
        · assumption
      · simp only [String.Slice.Pos.next, String.Slice.Pos.byte, String.Slice.getUTF8Byte,
          String.getUTF8Byte, String.Pos.Raw.byteIdx_add] at h₂ ⊢
        have := ByteArray.not_isUTF8FirstByte_of_isSome_utf8DecodeChar?
          (k := p'.byteIdx - p.offset.byteIdx) hp.2 ?_ ?_
        · simpa only [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt h₁)] using this
        · exact Nat.sub_pos_of_lt h₁
        · rw [Nat.sub_lt_iff_lt_add']
          · assumption
          · exact Nat.le_of_lt h₁
  · rename_i h'
    simp only [Pos.Raw.lt_iff, Nat.not_lt] at h'
    replace h' := Nat.le_trans h' h₂
    apply Nat.le_antisymm h'
    exact (p.next h).isValidForSlice.le_utf8ByteSize
termination_by s.utf8ByteSize.byteIdx - p'.byteIdx
decreasing_by omega

theorem String.Slice.Pos.next_eq_findNextPos {s : Slice} {p : s.Pos} (h) :
    p.next h = s.findNextPos p.offset
      (Nat.lt_of_le_of_ne p.isValidForSlice.le_utf8ByteSize (mt (Pos.ext ∘ Pos.Raw.ext) h)) := by
  rw [findNextPos, findNextPos.go_eq_next_of_le_of_lt]
  · simp
  · exact p.lt_next

@[simp]
theorem String.Slice.endPos_le_iff {s : Slice} {p : s.Pos} : s.endPos ≤ p ↔ p = s.endPos := by
  constructor
  · intro h
    ext
    exact Nat.le_antisymm p.isValidForSlice.le_utf8ByteSize h
  · rintro rfl
    exact Nat.le_refl _

theorem String.Slice.findNextPos.go_spec {s : Slice} {p} {p'} (h : p ≤ s.utf8ByteSize) :
    findNextPos.go s p = p' ↔ p ≤ p'.offset ∧ ∀ q, p ≤ q.offset → p' ≤ q := by
  fun_induction findNextPos.go
  · rename_i p hp hfb
    constructor
    · rintro rfl
      simp only [offset_pos, Pos.Raw.le_refl, true_and]
      intro q
      exact id
    · intro ⟨h₁, h₂⟩
      ext
      apply Nat.le_antisymm h₁
      apply h₂ (s.pos p (Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.mpr (.inr ⟨hp, hfb⟩)))
      exact Pos.Raw.le_refl
  · rename_i p hp hfb ih
    rw [ih hp]
    have ne (q : s.Pos) : p ≠ q.offset := by
      rintro rfl
      exact absurd (q.isUTF8FirstByte_byte (h := by intro; simp [*] at hp)) hfb
    have (q : s.Pos) := @Nat.le_iff_lt_or_eq p.byteIdx q.offset.byteIdx
    change ∀ q : s.Pos, p ≤ q.offset ↔ p.inc ≤ q.offset ∨ _ at this
    simp only [mt Pos.Raw.ext (ne _), or_false] at this
    simp [← this]
  · rename_i p hp
    cases show p = s.endPos.offset by ext; exact Nat.le_antisymm h (Nat.not_lt.mp hp)
    simp only [eq_comm, ← Pos.le_iff, endPos_le_iff, forall_eq, iff_self_and]
    rintro rfl
    exact Nat.le_refl _

theorem String.Slice.findNextPos_spec {s : Slice} {p} {h} {p'} :
    s.findNextPos p h = p' ↔ p < p'.offset ∧ ∀ q, p < q.offset → p' ≤ q := by
  rw [findNextPos, findNextPos.go_spec]
  · rfl
  · exact h

theorem String.Slice.Pos.prevAux.go_spec {s : Slice} {off hoff} {p : Pos.Raw} :
    @prevAux.go s off hoff = p ↔ p.IsValidForSlice s ∧ p.byteIdx ≤ off ∧
      ∀ q : s.Pos, q.offset.byteIdx ≤ off → q.offset ≤ p := by
  induction off, hoff using prevAux.go.induct with -- #10751
  | case1 off hoff hfb =>
    rw [go, dif_pos hfb]
    replace hfb := Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.mpr (.inr ⟨hoff, hfb⟩)
    constructor
    · rintro rfl
      refine ⟨hfb, Nat.le_refl _, ?_⟩
      intro q; exact id
    · intro ⟨h₁, h₂, h₃⟩
      ext
      apply Nat.le_antisymm _ h₂
      exact h₃ (s.pos _ hfb) (Nat.le_refl _)
  | case2 off hoff hfb _ ih =>
    rw [go, dif_neg hfb]; dsimp only
    rw [ih]
    have ne (q : Pos.Raw) (hq : q.IsValidForSlice s) : q ≠ ⟨off + 1⟩ := by
      rintro rfl
      simp only [Pos.Raw.isValidForSlice_iff_isUTF8FirstByte, Pos.Raw.ext_iff, Nat.ne_of_lt hoff,
        hfb, Pos.Raw.lt_iff, exists_false, or_self] at hq
    have (p : Pos.Raw) (hp : p.IsValidForSlice s) := @Nat.le_iff_lt_or_eq p.byteIdx off.succ
    simp only [ne_eq, Pos.Raw.ext_iff] at ne
    simp +contextual only [ne, or_false, Nat.lt_succ_iff] at this
    simp +contextual only [this, Pos.isValidForSlice, ← exists_prop]

/-- `p.prev h` is the greatest position `< p` -/
theorem String.Slice.Pos.prev_spec {s : Slice} {p p' : s.Pos} {h} :
    p.prev h = p' ↔ p' < p ∧ ∀ q : s.Pos, q < p → q ≤ p' := by
  have : 0 < p.offset.byteIdx := Nat.pos_of_ne_zero (by simpa [Pos.ext_iff] using h)
  simp only [prev, prevAux, Slice.Pos.ext_iff, prevAux.go_spec, Pos.isValidForSlice, true_and,
    Nat.le_sub_one_iff_lt, this, Pos.lt_iff, Pos.le_iff, Pos.Raw.lt_iff]

/-- `p.next h` is the smallest position `> p` -/
theorem String.Slice.Pos.next_spec {s : Slice} {p p' : s.Pos} {h} :
    p.next h = p' ↔ p < p' ∧ ∀ q : s.Pos, p < q → p' ≤ q := by
  simp only [next_eq_findNextPos, findNextPos_spec, Pos.lt_iff]

@[simp] theorem Char.utf8Size_ne_zero (c : Char) : c.utf8Size ≠ 0 := Nat.ne_of_gt c.utf8Size_pos
@[simp] theorem Char.zero_ne_utf8Size (c : Char) : c.utf8Size ≠ 0 := Nat.ne_of_gt c.utf8Size_pos

@[simp]
theorem String.Slice.Pos.next_ne_startPos {s : Slice} {p : s.Pos} {h} :
    p.next h ≠ s.startPos := by
  simp [Pos.ext_iff]

@[simp]
theorem String.ValidPos.next_ne_startValidPos {s : String} (p : s.ValidPos) {h} :
    p.next h ≠ s.startValidPos :=
  mt (congrArg (·.toSlice)) (Slice.Pos.next_ne_startPos (h := mt (congrArg (·.ofSlice)) h))

@[simp]
theorem String.Slice.Pos.next_prev {s : Slice} (p : s.Pos) (h) :
    (p.prev h).next (by simp) = p := by
  rw [next_spec]
  simp +singlePass only [← Decidable.not_imp_not]
  simpa [Pos.le_iff, Pos.lt_iff, Pos.Raw.le_iff] using (prev_spec (h := h)).mp rfl

@[simp]
theorem String.Slice.Pos.prev_next {s : Slice} (p : s.Pos) (h) :
    (p.next h).prev (by simp) = p := by
  rw [prev_spec]
  simp +singlePass only [← Decidable.not_imp_not]
  simpa [Pos.le_iff, Pos.lt_iff, Pos.Raw.le_iff] using (next_spec (h := h)).mp rfl

@[simp]
theorem String.ValidPos.next_prev {s : String} (p : s.ValidPos) (h) :
    (p.prev h).next (by simp) = p := by
  simp [next, prev]

@[simp]
theorem String.ValidPos.prev_next {s : String} (p : s.ValidPos) (h) :
    (p.next h).prev (by simp) = p := by
  simp [next, prev]

@[simp]
theorem String.ValidPos.get_cast (h : s = t) (h') :
    (String.ValidPos.cast p h).get h' = p.get (by cases h; exact h') := by
  cases h; rfl

@[simp]
theorem String.ValidPos.next_cast (h : s = t) (h') :
    (String.ValidPos.cast p h).next h' = (p.next (by cases h; exact h')).cast h := by
  cases h; rfl

@[simp]
theorem String.ValidPos.prev_cast (h : s = t) (h') :
    (String.ValidPos.cast p h).prev h' = (p.prev (by cases h; exact h')).cast h := by
  cases h; rfl

@[simp]
theorem String.ValidPos.cast_cast (h : s = t) (h' : t = u) :
    (String.ValidPos.cast p h).cast h' = p.cast (h.trans h') := rfl

@[simp]
theorem String.ValidPos.cast_eq_endValidPos (h : s = t) :
    String.ValidPos.cast p h = t.endValidPos ↔ p = s.endValidPos := by
  cases h; rfl

@[simp]
theorem String.ValidPos.cast_eq_startValidPos (h : s = t) :
    String.ValidPos.cast p h = t.startValidPos ↔ p = s.startValidPos := by
  cases h; rfl

@[simp]
theorem String.prev_posBetween_push {s t : String} {c : Char} (h) :
    ((s.push c).posBetween t).prev h =
      (s.posBetween (String.singleton c ++ t)).cast
        (by simp only [String.push_eq_append, String.append_assoc]) := by
  conv => rhs; rw [← ValidPos.prev_next (String.posBetween _ _) (by simp)]
  simp

theorem String.posBetween_congr {s₁ s₂ t₁ t₂ : String} (hs : s₁ = s₂) (ht : t₁ = t₂) :
    s₁.posBetween t₁ = (s₂.posBetween t₂).cast (by rw [hs, ht]) := by
  subst hs ht; rfl

@[simp]
theorem String.get_posBetween_mk_cons_append {s t : String} {c : Char} {cs : List Char} (h) :
    (s.posBetween (no_index (String.mk (c :: cs)) ++ t)).get h = c := by
  have : mk (c :: cs) ++ t = String.singleton c ++ (mk cs ++ t) := by
    simp [ByteArray.append_assoc, List.utf8Encode_cons (l := cs), ← String.bytes_inj]
  simp only [String.posBetween_congr rfl this, ValidPos.get_cast,
    String.get_posBetween_singleton_append]

@[simp]
theorem String.next_posBetween_mk_cons_append {s t : String} {c : Char} {cs : List Char} (h) :
    (s.posBetween (no_index (String.mk (c :: cs)) ++ t)).next h =
      ((s.push c).posBetween (String.mk cs ++ t)).cast (by
        simp [ByteArray.append_assoc, List.utf8Encode_cons (l := cs), ← String.bytes_inj]) := by
  have : mk (c :: cs) ++ t = String.singleton c ++ (mk cs ++ t) := by
    simp [ByteArray.append_assoc, List.utf8Encode_cons (l := cs), ← String.bytes_inj]
  simp only [String.posBetween_congr rfl this, ValidPos.next_cast, ValidPos.cast_cast,
    String.next_posBetween_singleton_append]

theorem String.startValidPos_eq_posBetween (s : String) :
    s.startValidPos = "".posBetween s := rfl

theorem String.startValidPos_eq_posBetween' (s : String) :
    s.startValidPos = ("".posBetween s).cast (by simp) := rfl

theorem String.endValidPos_eq_posBetween (s : String) :
    s.endValidPos = (s.posBetween "").cast (by simp) := rfl

def encodeHex (n val : Nat) : String :=
  match n with
  | 0 => ""
  | k + 1 => (String.singleton <| Nat.digitChar (val / 16 ^ k % 16)) ++ encodeHex k val

@[simp]
theorem checkLowerHex_cast {s t : String} {p : t.ValidPos} (h : t = s) :
    Lean.checkLowerHex n s (p.cast h) = Lean.checkLowerHex n t p := by
  cases h; rfl

@[simp]
theorem parseLowerHex_cast {s t : String} {p : t.ValidPos} (h : t = s) (h') :
    Lean.parseLowerHex n s (p.cast h) h' i = Lean.parseLowerHex n t p (by cases h; exact h') i := by
  cases h; rfl

theorem String.singleton_append_cases (s : String) :
    s = "" ∨ ∃ c s', s = String.singleton c ++ s' := by
  simp only [data_empty, ← String.data_inj, data_append, data_singleton, List.singleton_append]
  rcases s.data with _ | ⟨a, b⟩
  · simp
  · right
    exists a, b.asString
    simp

theorem Nat.digitChar_eq (n : Nat) (h : n < 16) : n.digitChar =
    if h : n < 10 then
      ⟨UInt32.ofNatLT (48 + n) (by grind), by grind [UInt32.toNat_ofNatLT]⟩
    else
      ⟨UInt32.ofNatLT (87 + n) (by grind), by grind [UInt32.toNat_ofNatLT]⟩ := by
  decide +revert

theorem pushHex_eq_encodeHex {s : String} {n : Nat} {i : UInt32} (h : n ≤ 8) :
    s.pushHex n i = s ++ encodeHex n i.toNat := by
  fun_induction String.pushHex
  · simp [encodeHex]
  · rename_i s k i' ih
    rw [ih (Nat.le_of_succ_le h)]
    rw [encodeHex, ← String.append_assoc, String.append_singleton]
    congr 2
    have : i.toNat / 16 ^ k % 16 = i'.toNat := by
      simp only [i', UInt32.toNat_and, UInt32.reduceToNat]
      rw [show 15 = 2^4-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      congr 1
      rw [UInt32.toNat_shiftRight, UInt32.toNat_mul, UInt32.toNat_ofNat',
        Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt (by simp; omega),
        Nat.mod_eq_of_lt (by simp; omega)]
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
      simp only [UInt32.reduceToNat, Nat.reducePow]
    rw [this]
    show String.digitChar _ ?hlt16 = _
    have hlt16 := ?hlt16
    change String.digitChar i' hlt16 = _
    clear ih h this
    clear_value i'
    rcases i' with ⟨i, h⟩
    change i < 16 at hlt16
    cases (show h = Nat.lt_trans hlt16 (by decide) from rfl)
    decide +revert

theorem checkLowerHex_encodeHex :
    Lean.checkLowerHex n (s ++ (encodeHex n val ++ t)) (String.posBetween _ _) = true := by
  fun_induction encodeHex generalizing s
  · rfl
  · rename_i k ih
    rw [String.append_assoc]
    suffices (val / 16 ^ k % 16).digitChar.isDigit = true ∨
        97 ≤ (val / 16 ^ k % 16).digitChar.val ∧ (val / 16 ^ k % 16).digitChar.val ≤ 102 by
      simpa [Lean.checkLowerHex, ih]
    have h'' : val / 16 ^ k % 16 < 16 := Nat.mod_lt _ (by decide)
    generalize val / 16 ^ k % 16 = c at h''
    decide +revert

/-
{
      offset :=
        {
          byteIdx :=
            ((s.push 'x').posBetween
                    (encodeHex 2 pc.val.toNat ++
                      (pt.mangle ++
                        mangleSuffix (b || tailUnderscore (String.singleton pc ++ pt)) nm))).offset.byteIdx +
              2 },
      isValid := ⋯ }
-/

@[simp]
theorem utf8ByteSize_encodeHex {n val : Nat} :
    (encodeHex n val).utf8ByteSize = n := by
  induction n with
  | zero => simp [encodeHex]
  | succ k ih =>
    simp only [encodeHex, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih,
      Nat.add_comm k, Nat.add_right_cancel_iff]
    have : val / 16 ^ k % 16 < 16 := Nat.mod_lt _ (by decide)
    generalize val / 16 ^ k % 16 = i at this
    decide +revert

theorem encodeHex_thing {ss : String} {hvalid} (h : ss = s ++ (encodeHex n val ++ t)) :
    (String.ValidPos.mk (String.Pos.Raw.mk
        ((String.posBetween s (encodeHex n val ++ t)).offset.byteIdx + n))
      hvalid : ss.ValidPos) =
      (String.posBetween (s ++ encodeHex n val) t).cast (by rw [h, String.append_assoc]) := by
  ext; simp only [String.posBetween, String.byteIdx_endPos, String.ValidPos.offset_cast,
    String.utf8ByteSize_append, utf8ByteSize_encodeHex]

theorem Nat.shiftLeft_or_eq_add (a b c : Nat) (h : c < 2 ^ b) :
    (a <<< b) ||| c = a * 2 ^ b + c := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw (occs := [2]) [Nat.testBit_eq_decide_div_mod_eq]
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [testBit_or, testBit_shiftLeft, ge_iff_le, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  by_cases hb : b ≤ i
  · have : c.testBit i = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not, Nat.div_eq_of_lt]
      · decide
      · exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hb)
    simp only [hb, true_and, this, Bool.false_eq_true, or_false]
    obtain ⟨i, rfl⟩ := hb.dest
    simp [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_comm _ c, Nat.add_mul_div_right,
      Nat.two_pow_pos, Nat.div_eq_of_lt h, Nat.testBit_eq_decide_div_mod_eq]
  · simp only [hb, false_and, false_or]
    simp only [Nat.not_le] at hb
    obtain ⟨d, rfl⟩ := hb.dest
    rw [Nat.succ_add, ← Nat.add_succ, Nat.pow_add', ← Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), ← Nat.add_mod_mod, Nat.pow_succ,
      ← Nat.mul_assoc, Nat.mul_mod_left, Nat.add_zero, testBit_eq_decide_div_mod_eq,
      decide_eq_true_eq]

theorem parseLowerHex_encodeHex (h') :
    Lean.parseLowerHex n (s ++ (encodeHex n val ++ t)) (String.posBetween _ _) h' i =
        i * 16 ^ n + val % 16 ^ n := by
  fun_induction encodeHex generalizing s i
  · simp_all [Lean.parseLowerHex, Nat.mod_one]
  · rename_i k ih
    simp only [Nat.succ_eq_add_one, String.posBetween_congr rfl String.append_assoc,
      parseLowerHex_cast]
    simp only [Lean.parseLowerHex, String.get_posBetween_singleton_append,
      String.next_posBetween_singleton_append, parseLowerHex_cast, ih]
    have h'' : val / 16 ^ k % 16 < 16 := Nat.mod_lt _ (by decide)
    generalize hc : val / 16 ^ k % 16 = c at h''
    rw [Char.isDigit]
    simp only [ge_iff_le, Bool.and_eq_true, decide_eq_true_eq]
    have this (a h) := Nat.shiftLeft_or_eq_add i 4 a h
    simp only [Nat.reducePow] at this
    rw [Nat.pow_succ, Nat.mul_comm _ 16, ← Nat.mul_assoc, ← apply_ite (· + _),
      Nat.mul_comm 16, Nat.mod_mul, Nat.add_comm (val % 16 ^ k), ← Nat.add_assoc,
      Nat.add_right_cancel_iff]
    rw [hc, Nat.mul_comm _ c, ← Nat.add_mul, ← this c h'']; clear this hc
    split <;> (congr; decide +revert)

def Char.mangle (c : Char) : String :=
  if c.isAlpha || c.isDigit then
    .singleton c
  else if c = '_' then
    "__"
  else if c.toNat < 0x100 then
    "_x".pushHex 2 c.val
  else if c.toNat < 0x10000 then
    "_u".pushHex 4 c.val
  else
    "_U".pushHex 8 c.val

@[simp]
theorem Char.mangle_u : Char.mangle '_' = .singleton '_' ++ .singleton '_' := rfl

theorem String.length_mk {s : List Char} : (no_index (String.mk s)).length = s.length := by
  simp

@[simp]
theorem Char.length_mangle_pos (c : Char) : 0 < c.mangle.length := by
  fun_cases Char.mangle <;> simp +arith [pushHex_eq_encodeHex, String.length_mk]

@[simp]
theorem String.push_empty : "".push c = String.singleton c := rfl

theorem String.push_append (s : String) : s.push c ++ t = s ++ (singleton c ++ t) := by
  simp only [String.push_eq_append, String.append_assoc]

theorem String.append_push (s : String) : s ++ t.push c = (s ++ t).push c := by
  simp only [String.push_eq_append, String.append_assoc]

theorem String.mangleAux_cast {s t r : String} (h : s = t) (p : s.ValidPos) :
    String.mangleAux t (p.cast h) r = String.mangleAux s p r := by
  cases h; rfl

theorem String.mangleAux_normalize :
    mangleAux (s ++ t) (posBetween s t) r =
      r ++ mangleAux t t.startValidPos "" := by
  obtain rfl | ⟨c, s', rfl⟩ := t.singleton_append_cases
  · rw [String.mangleAux, String.mangleAux, dif_pos (by simp), dif_pos (by simp), append_empty]
  unfold String.mangleAux
  rw [dif_neg (by simp), dif_neg (by simp)]
  extract_lets c' p' c2' p2'
  have hc' : c' = c := by simp [c']
  have hc2' : c2' = c := by simp [c2', String.get_startValidPos]
  simp only [hc', hc2']
  have ih (r : String) := String.mangleAux_normalize (s := s.push c) (t := s') (r := r)
  have ih' (r : String) := String.mangleAux_normalize (s := String.singleton c) (t := s') (r := r)
  conv at ih => intro r; tactic =>
    rw [← mangleAux_cast, ← next_posBetween_singleton_append (by simp)]; rw [push_append]
  have hp2' : p2' = String.posBetween _ _ := by
    simp [p2', String.startValidPos_eq_posBetween]
  rw [← hp2'] at ih'
  split
  · conv => lhs; rw [ih]
    conv => rhs; rw [ih']
    simp only [String.push_append, String.push_empty]
  split
  · conv => lhs; rw [ih]
    conv => rhs; rw [ih']
    simp only [String.empty_append, String.append_assoc]
  split
  · conv => lhs; rw [ih]
    conv => rhs; rw [ih']
    simp +zetaDelta only [Nat.reduceLeDiff, pushHex_eq_encodeHex, append_assoc, empty_append]
  split
  · conv => lhs; rw [ih]
    conv => rhs; rw [ih']
    simp +zetaDelta only [Nat.reduceLeDiff, pushHex_eq_encodeHex, append_assoc, empty_append]
  · conv => lhs; rw [ih]
    conv => rhs; rw [ih']
    simp +zetaDelta only [Nat.reduceLeDiff, pushHex_eq_encodeHex, append_assoc, empty_append]
termination_by t.length

theorem String.mangleAux_empty : mangleAux s s.endValidPos r = r := by
  simp [String.mangleAux]

@[simp]
theorem String.mangle_empty : mangle "" = "" := by
  simp [String.mangle, String.mangleAux]

theorem String.next_startValidPos_singleton :
    (String.singleton c).startValidPos.next (by simp) = (String.singleton c).endValidPos := by
  simp [startValidPos_eq_posBetween]
  simp only [posBetween_congr rfl (append_empty (s := singleton c)).symm]
  simp only [ValidPos.next_cast, next_posBetween_singleton_append, push_empty, ValidPos.cast_rfl,
    ValidPos.cast_eq_endValidPos]
  apply (posBetween_eq_endValidPos_iff _ _).mpr
  rfl

@[simp]
theorem String.mangle_singleton_append :
    mangle (String.singleton c ++ t) = c.mangle ++ t.mangle := by
  rw [String.mangle, Char.mangle]
  unfold String.mangleAux
  rw [dif_neg (by simp)]
  extract_lets c' p
  have hc' : c' = c := by simp [c', get_startValidPos]
  have hp : p = String.posBetween _ _ := by simp [p, startValidPos_eq_posBetween]
  simp only [hc', empty_append, push_empty, hp, String.mangleAux_normalize]
  (repeat' split) <;> rfl

@[simp]
theorem Char.mangle_ne_empty : Char.mangle c ≠ "" := by
  rw [Char.mangle]
  split
  · simp
  split
  · simp
  split
  · rw [pushHex_eq_encodeHex (by decide)]
    simp
  split
  · rw [pushHex_eq_encodeHex (by decide)]
    simp
  · rw [pushHex_eq_encodeHex (by decide)]
    simp

@[simp]
theorem String.mangle_eq_empty : mangle s = "" ↔ s = "" := by
  obtain rfl | ⟨c, s, rfl⟩ := s.singleton_append_cases <;> simp

@[simp]
theorem String.pushn_zero : String.pushn s c 0 = s := rfl

@[simp]
theorem String.pushn_one : String.pushn s c 1 = s.push c := rfl

theorem String.pushn_succ : String.pushn s c (n + 1) = (s.pushn c n).push c := rfl

theorem String.pushn_succ' : String.pushn s c (n + 1) = (s.push c).pushn c n := by
  rw [String.pushn, Nat.repeat_eq_repeatTR, Nat.repeatTR, Nat.repeatTR.loop]
  rw [String.pushn, Nat.repeat_eq_repeatTR, Nat.repeatTR]

@[simp]
theorem String.pushn_eq_empty : String.pushn s c n = "" ↔ s = "" ∧ n = 0 := by
  cases n <;> simp [pushn_succ]

@[simp]
theorem String.empty_eq : "" = s ↔ s = "" := eq_comm

@[simp]
theorem String.push_inj {s t : String} {a b : Char} : s.push a = t.push b ↔ s = t ∧ a = b := by
  simp [← data_inj, ← List.concat_eq_append, List.concat_inj]

@[simp]
theorem String.singleton_append_inj {a b : Char} {s t : String} :
    singleton a ++ s = singleton b ++ t ↔ a = b ∧ s = t := by
  simp [← data_inj]

@[simp]
theorem String.singleton_inj {a b : Char} : singleton a = singleton b ↔ a = b := by
  simp [← data_inj]

@[simp]
theorem String.singleton_eq_push_iff {s : String} {a b : Char} :
    singleton a = s.push b ↔ s = "" ∧ a = b := by
  simpa using String.push_inj (s := "")

@[simp]
theorem String.push_eq_singleton_iff {s : String} {a b : Char} :
    s.push a = singleton b ↔ s = "" ∧ a = b := by
  simpa using String.push_inj (t := "")

theorem String.append_eq_pushn_empty_iff :
    s ++ t = pushn "" c n ↔ ∃ i j, i + j = n ∧ s = pushn "" c i ∧ t = pushn "" c j := by
  induction n generalizing s t with
  | zero => simp [and_assoc]
  | succ k ih =>
    rw [pushn_succ]
    induction t using String.push_induction
    · induction s using String.push_induction
      · simp
      · simp [pushn_succ]
    · rw [append_push]
      simp only [push_inj, ih]
      constructor
      · rintro ⟨⟨i, j, rfl, rfl, rfl⟩, rfl⟩
        exists i, j + 1
      · rintro ⟨i, j, hk, rfl, hj⟩
        rcases j with _ | j
        · simp at hj
        · cases hk
          simp only [pushn_succ, push_inj] at hj
          exact ⟨⟨i, j, rfl, rfl, hj.1⟩, hj.2⟩

@[simp]
theorem String.data_pushn (s : String) (c : Char) (n : Nat) :
    (s.pushn c n).data = s.data ++ List.replicate n c := by
  induction n <;> simp_all [String.pushn_succ, List.replicate_succ']

@[simp]
theorem String.mk_eq_pushn_empty_iff (s : List Char) (c : Char) :
    no_index (String.mk s) = pushn "" c n ↔ s = List.replicate n c := by
  simp [← data_inj]

theorem String.push_eq_pushn_iff {s : String} :
    s.push c = pushn "" c' n ↔ c = c' ∧ ∃ i, i + 1 = n ∧ s = pushn "" c' i := by
  rcases n with _ | n
  · simp
  · simp [pushn_succ, and_comm]

@[simp]
theorem String.singleton_eq_pushn_empty_iff :
    singleton c = pushn "" c' n ↔ c = c' ∧ n = 1 := by
  rw [← push_empty]
  rcases n with _ | _ | n <;> simp [pushn_succ]

theorem String.pushn_normalize : String.pushn s c n = s ++ "".pushn c n := by
  simp only [String.pushn, Nat.repeat_eq_repeatTR, Nat.repeatTR]
  induction n generalizing s with
  | zero => simp [Nat.repeatTR.loop]
  | succ k ih =>
    simp only [Nat.repeatTR.loop]
    conv => lhs; rw [ih]
    conv => rhs; rw [ih]
    simp [push_append]

theorem String.pushn_empty_succ : pushn "" c (n + 1) = singleton c ++ pushn "" c n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pushn_succ', pushn_normalize, push_empty, ih]

theorem String.ValidPos.lt_trans {p₁ p₂ p₃ : String.ValidPos s} :
    p₁ < p₂ → p₂ < p₃ → p₁ < p₃ := Nat.lt_trans

def adigit (n : Fin 10) : Char :=
  ⟨UInt32.ofNatLT (n.val + 48) (by grind), by grind [UInt32.toNat_ofNatLT]⟩

@[simp]
theorem isDigit_adigit (i : Fin 10) : (adigit i).isDigit := by
  decide +revert

@[simp]
theorem isDigit_ne_u (i : Fin 10) : adigit i ≠ '_' := by
  decide +revert

@[simp]
theorem val_adigit (i : Fin 10) : (adigit i).val =
    UInt32.ofNatLT i (Nat.lt_trans i.isLt (by decide)) + 48 := by
  decide +revert

@[simp]
theorem adigit_eq_zero_iff (i : Fin 10) : adigit i = '0' ↔ i = 0 := by
  decide +revert

def digitsToString (l : List (Fin 10)) : String :=
  match l with
  | [] => ""
  | n :: ns => .singleton (adigit n) ++ digitsToString ns

theorem digitsToString_concat {l : List (Fin 10)} (i : Fin 10) :
    digitsToString (l ++ [i]) = (digitsToString l).push i.val.digitChar := by
  fun_induction digitsToString
  · decide +revert
  · rename_i n ns ih
    simp [digitsToString, ih, String.append_push]

def digitsToNat (l : List (Fin 10)) (acc : Nat) : Nat :=
  match l with
  | [] => acc
  | n :: ns => digitsToNat ns (acc * 10 + n)

theorem digitsToNat_concat {l : List (Fin 10)} (i : Fin 10) :
    digitsToNat (l ++ [i]) acc = digitsToNat l acc * 10 + i.val := by
  fun_induction digitsToNat <;> simp_all [digitsToNat]

def IsDigits (l : List (Fin 10)) : Prop :=
  l ≠ [] ∧ (l.head? = some 0 → l = [0])

theorem Nat.toDigitsCore_normalize (base fuel val : Nat) (acc : List Char) :
    Nat.toDigitsCore base fuel val acc = Nat.toDigitsCore base fuel val [] ++ acc := by
  induction fuel generalizing val acc
  · rfl
  · rename_i ih
    simp only [toDigitsCore]
    conv => lhs; rw [ih]
    conv => rhs; rw [ih]
    simp [apply_ite (· ++ acc)]

theorem Nat.exists_toDigitsCore_eq (h : val < fuel) :
    ∃ l, IsDigits l ∧ digitsToString l = (Nat.toDigitsCore 10 fuel val []).asString ∧
      digitsToNat l 0 = val := by
  induction fuel generalizing val with
  | zero => nomatch h
  | succ k ih =>
    rw [Nat.toDigitsCore]
    split
    · rename_i h'
      simp only [Nat.div_eq_zero_iff, reduceCtorEq, false_or] at h'
      refine ⟨[Fin.mk val h'], ?_⟩
      simp only [digitsToString, String.append_empty, ← String.data_inj, String.data_singleton,
        List.data_asString, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_⟩
      · simp [IsDigits]
      · clear h; decide +revert
      · simp [digitsToNat]
    · rename_i h'
      simp only [Nat.div_eq_zero_iff, reduceCtorEq, false_or, Nat.not_lt] at h'
      rw [Nat.lt_add_one_iff] at h
      specialize ih (Nat.lt_of_lt_of_le (Nat.div_lt_self (k := 10) (Nat.zero_lt_of_lt h') (by decide)) h)
      obtain ⟨l, ⟨hd₁, hd₂⟩, hl₁, hl₂⟩ := ih
      refine ⟨l ++ [Fin.ofNat 10 val], ?_, ?_⟩
      · obtain ⟨a, b, rfl⟩ := List.ne_nil_iff_exists_cons.mp hd₁
        grind [IsDigits, digitsToNat]
      · rw [toDigitsCore_normalize]
        simp [digitsToString_concat, Fin.val_ofNat, digitsToNat_concat, ← String.data_inj, ← hl₁,
          hl₂, Nat.div_add_mod']

theorem Nat.exists_repr_eq (n : Nat) : ∃ l, IsDigits l ∧ digitsToString l = n.repr ∧ digitsToNat l 0 = n := by
  rw [Nat.repr, toDigits]
  exact Nat.exists_toDigitsCore_eq n.lt_add_one

namespace Lean.Name

@[simp]
theorem mangleAux_eq_empty : mangleAux nm = "" ↔ nm = .anonymous := by
  constructor
  rotate_left
  · rintro rfl; rfl
  fun_cases mangleAux
  · simp
  · simp
  · rename_i s m h
    intro hm
    simp only [String.mangle_eq_empty, m] at hm
    cases hm
    have : m = "" := by simp [m]
    rw [this] at h
    simp [Lean.checkDisambiguation] at h
  · split <;> simp
  · simp
  · simp

-- "dummy" append
def extend (n n' : Name) : Name :=
  match n' with
  | .anonymous => n
  | .str n' s => (n.extend n').str s
  | .num n' i => (n.extend n').num i

-- "n +-+ n'.reverse"
def extendRev (n n' : Name) : Name :=
  match n' with
  | .anonymous => n
  | .str n' s => (n.str s).extendRev n'
  | .num n' i => (n.num i).extendRev n'

attribute [simp] extend.eq_1 extend.eq_2 extend.eq_3
attribute [simp] extendRev.eq_1 extendRev.eq_2 extendRev.eq_3

local infixl:65 " +-+ " => extend
local infixl:65 " +-+! " => extendRev

@[simp]
theorem anonymous_extend (n : Name) : anonymous.extend n = n := by
  induction n <;> simp_all

theorem extend_assoc (n₁ n₂ n₃ : Name) : n₁ +-+ n₂ +-+ n₃ = n₁ +-+ (n₂ +-+ n₃) := by
  induction n₃ <;> simp_all

theorem extendRev_extend (n₁ n₂ n₃ : Name) : n₁ +-+! (n₃ +-+ n₂) = n₁ +-+! n₂ +-+! n₃ := by
  induction n₂ generalizing n₁ <;> simp_all

theorem extend_extendRev (n₁ n₂ n₃ : Name) : n₁ +-+ (n₂ +-+! n₃) = n₁ +-+ n₂ +-+! n₃ := by
  induction n₃ generalizing n₁ n₂ <;> simp_all

theorem extendRev_eq_extend (n₁ n₂ : Name) : n₁ +-+! n₂ = n₁ +-+ (anonymous +-+! n₂) := by
  rw [extend_extendRev, extend]

theorem extendRev_extendRev (n₁ n₂ n₃ : Name) : n₁ +-+! (n₃ +-+! n₂) = n₁ +-+ n₂ +-+! n₃ := by
  conv => rhs; rw [extendRev_eq_extend, extend_extendRev]
  induction n₂ generalizing n₁ n₃ <;> simp_all

def prependStr (s : String) (n : Name) : Name :=
  match n with
  | .anonymous => .anonymous
  | .str .anonymous s' => .str .anonymous (s ++ s')
  | .str n s' => .str (n.prependStr s) s'
  | .num n i => .num (n.prependStr s) i

attribute [simp] prependStr.eq_1 prependStr.eq_2 prependStr.eq_4

@[simp]
theorem prependStr_empty (n : Name) : n.prependStr "" = n := by
  fun_induction prependStr <;> simp_all

@[simp]
theorem prependStr_eq_anonymous (n : Name) : n.prependStr s = anonymous ↔ n = anonymous := by
  fun_cases prependStr <;> simp

@[simp]
theorem extend_eq_anonymous (n n' : Name) :
    n +-+ n' = anonymous ↔ n = anonymous ∧ n' = anonymous := by
  cases n' <;> simp

@[simp]
theorem prependStr_str_anonymous_extend (s s' : String) (n : Name) :
    (str anonymous s' +-+ n).prependStr s = str anonymous (s ++ s') +-+ n := by
  induction n <;> simp_all [prependStr]

@[simp]
theorem prependStr_str_anonymous_extendRev (s s' : String) (n : Name) :
    (str anonymous s' +-+! n).prependStr s = str anonymous (s ++ s') +-+! n := by
  rw [extendRev_eq_extend, prependStr_str_anonymous_extend, ← extendRev_eq_extend]

@[simp]
theorem prependStr_prependStr (n : Name) :
    (n.prependStr s).prependStr s' = n.prependStr (s' ++ s) := by
  fun_induction prependStr s n <;> simp_all [String.append_assoc, prependStr]

@[simp]
theorem unmangleAux_cast {s t : String} (h : s = t) {p : s.ValidPos}
    {res : Name} {acc : String} {ucount : Nat} :
    unmangleAux t (p.cast h) res acc ucount = unmangleAux s p res acc ucount := by
  cases h; rfl

@[simp]
theorem unmangleAux_nameStart_cast {s t : String} (h : s = t) {p : s.ValidPos} {res : Name} :
    unmangleAux.nameStart t (p.cast h) res = unmangleAux.nameStart s p res := by
  cases h; rfl

@[simp]
theorem unmangleAux_decodeNum_cast {s t : String} (h : s = t) {p : s.ValidPos}
    {res : Name} {n : Nat} :
    unmangleAux.decodeNum t (p.cast h) res n = unmangleAux.decodeNum s p res n := by
  cases h; rfl

macro "term_tactic" : tactic =>
  `(tactic| all_goals first
    | with_reducible apply String.ValidPos.remainingBytes_next_lt
    | apply String.ValidPos.remainingBytes_next_lt_of_lt
      apply String.ValidPos.lt_trans (String.ValidPos.lt_next _)
      first
      | with_reducible apply String.ValidPos.lt_next _
      | apply Nat.lt_add_of_pos_right (by decide))

/-theorem unmangleAux_normalize2 {s : String} {p : s.ValidPos}
    (res : Name) (acc : String) {ucount : Nat} :
    unmangleAux s p res acc (ucount + 2) = res +-+ (unmangleAux s p .anonymous "" ucount).prependStr acc := by-/

mutual

theorem unmangleAux_normalize {s : String} {p : s.ValidPos}
    (res : Name) (acc : String) {ucount : Nat} :
    unmangleAux s p res acc ucount = res +-+ (unmangleAux s p .anonymous "" ucount).prependStr acc := by
  fun_cases unmangleAux s p res acc ucount
  · rw [unmangleAux, dif_pos ‹_›, prependStr, extend, extend, String.pushn_normalize]
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_pos ‹_›]
    rw [unmangleAux_normalize]
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_pos ‹_›]
    conv => lhs; rw [unmangleAux_normalize]
    conv => rhs; rw [unmangleAux_normalize]
    rw [anonymous_extend, String.pushn_normalize, prependStr_prependStr, String.append_push]
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg ‹_›, if_pos ‹_›, dif_pos ‹_›]
    conv => lhs; rw [unmangleAux_normalize]
    conv => rhs; rw [unmangleAux_normalize]
    rw [prependStr_empty, prependStr_str_anonymous_extend, ← extend_assoc, extend, extend,
      ← String.pushn_normalize]
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg ‹_›, if_pos ‹_›, dif_neg ‹_›]
    conv => lhs; rw [unmangleAux_decodeNum_normalize]
    conv => rhs; rw [unmangleAux_decodeNum_normalize]
    rw [prependStr_str_anonymous_extend, ← String.pushn_normalize, ← extend_assoc, extend, extend]
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg ‹_›, if_neg ‹_›, dif_pos ‹_›]
    conv => lhs; rw [unmangleAux_normalize]
    conv => rhs; rw [unmangleAux_normalize]
    rw [anonymous_extend, prependStr_prependStr, String.append_push, ← String.pushn_normalize]
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg ‹_›, if_neg ‹_›, dif_neg ‹_›, dif_pos ‹_›]
    conv => lhs; rw [unmangleAux_normalize]
    conv => rhs; rw [unmangleAux_normalize]
    rw [anonymous_extend, prependStr_prependStr, String.append_push, ← String.pushn_normalize]
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg ‹_›, if_neg ‹_›, dif_neg ‹_›, dif_neg ‹_›, dif_pos ‹_›]
    conv => lhs; rw [unmangleAux_normalize]
    conv => rhs; rw [unmangleAux_normalize]
    rw [anonymous_extend, prependStr_prependStr, String.append_push, ← String.pushn_normalize]
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg ‹_›, if_neg ‹_›, dif_neg ‹_›, dif_neg ‹_›, dif_neg ‹_›]
    conv => lhs; rw [unmangleAux_normalize]
    conv => rhs; rw [unmangleAux_normalize]
    rw [prependStr_str_anonymous_extend, String.append_empty, ← extend_assoc, extend, extend]
termination_by p.remainingBytes
decreasing_by term_tactic

theorem unmangleAux_decodeNum_normalize {s : String} {p : s.ValidPos} (res : Name) {i : Nat} :
    unmangleAux.decodeNum s p res i = res +-+ unmangleAux.decodeNum s p .anonymous i := by
  fun_cases unmangleAux.decodeNum s p res i
  · rw [unmangleAux.decodeNum, dif_pos ‹_›, extend, extend]
  · rw [unmangleAux.decodeNum.eq_def _ _ anonymous, dif_neg ‹_›, if_pos ‹_›]
    rw [unmangleAux_decodeNum_normalize]
  · rw [unmangleAux.decodeNum, dif_neg ‹_›, if_neg ‹_›, dif_pos ‹_›]
    rfl
  · rw [unmangleAux.decodeNum, dif_neg ‹_›, if_neg ‹_›, dif_neg ‹_›]
    conv => lhs; rw [unmangleAux_nameStart_normalize]
    conv => rhs; rw [unmangleAux_nameStart_normalize]
    rw [← extend_assoc]
    rfl
termination_by p.remainingBytes
decreasing_by term_tactic

theorem unmangleAux_nameStart_normalize {s : String} {p : s.ValidPos} (res : Name) :
    unmangleAux.nameStart s p res = res +-+ unmangleAux.nameStart s p .anonymous := by
  fun_cases unmangleAux.nameStart s p res
  · rw [unmangleAux.nameStart, dif_pos ‹_›, extend]
  · rw [unmangleAux.nameStart, dif_neg ‹_›, if_pos ‹_›, dif_pos ‹_›]
    rw [unmangleAux_normalize, prependStr_empty]
  · rw [unmangleAux.nameStart, dif_neg ‹_›, if_pos ‹_›, dif_neg ‹_›]
    rw [unmangleAux_decodeNum_normalize]
  · rw [unmangleAux.nameStart, dif_neg ‹_›, if_neg ‹_›, if_pos ‹_›]
    rw [unmangleAux_normalize, prependStr_empty]
  · rw [unmangleAux.nameStart, dif_neg ‹_›, if_neg ‹_›, if_neg ‹_›]
    conv => lhs; rw [unmangleAux_normalize]
    conv => rhs; rw [unmangleAux_normalize]
    rw [anonymous_extend]
termination_by p.remainingBytes
decreasing_by term_tactic

end

def tailUnderscore (s : String) : Bool :=
  ∃ h, (s.endValidPos.prev h).get (by simp) = '_'

theorem tailUnderscore_def {s : String} :
    tailUnderscore s ↔ ∃ t : String, s = t.push '_' := by
  simp only [tailUnderscore, ne_eq, decide_eq_true_eq]
  constructor
  · intro ⟨h, h'⟩
    refine ⟨s.startValidPos.extract (s.endValidPos.prev h), ?_⟩
    simp only [String.ValidPos.extract, String.offset_startValidPos, String.Pos.Raw.byteIdx_zero,
      ← String.bytes_inj, String.bytes_push, List.utf8Encode, List.flatMap_singleton]
    rw [String.ValidPos.get, String.Slice.Pos.get, String.decodeChar] at h'
    simp only [String.toSlice, String.offset_startValidPos, String.Pos.Raw.byteIdx_zero,
      String.ValidPos.offset_toSlice, Nat.zero_add] at h'
    rw [← h', ByteArray.utf8EncodeChar_utf8DecodeChar]
    simp only [ByteArray.extract_append_extract, Nat.zero_le, Nat.min_eq_left, Nat.le_add_right,
      Nat.max_eq_right]
    conv => lhs; rw [← s.bytes.extract_zero_size]
    congr
    refine Eq.trans (b := ((s.endValidPos.prev h).next (by simp)).offset.byteIdx) ?_ ?_
    · simp
    · simp [String.ValidPos.next, String.Slice.Pos.get, String.decodeChar]
  · rintro ⟨t, rfl⟩
    simp only [String.endValidPos_eq_posBetween, String.ValidPos.prev_cast,
      String.prev_posBetween_push, String.ValidPos.cast_cast, String.ValidPos.cast_rfl,
      String.get_posBetween_singleton_append, exists_prop, and_true]
    simp [String.ValidPos.ext_iff, String.posBetween]

@[simp]
theorem tailUnderscore_empty : tailUnderscore "" = false := rfl

@[simp]
theorem tailUnderscore_u : tailUnderscore "_" = true := rfl

theorem tailUnderscore_singleton_append {c : Char} {s : String} (h : c ≠ '_') :
    tailUnderscore (String.singleton c ++ s) = tailUnderscore s := by
  rw [Bool.eq_iff_iff, tailUnderscore_def, tailUnderscore_def]
  simp only [← String.data_inj, String.data_append, String.data_singleton,
    List.cons_append, List.nil_append, String.data_push]
  constructor
  · rintro ⟨t, ht⟩
    rcases htd : t.data with _ | ⟨_, tt⟩
    · simp_all
    · refine ⟨tt.asString, ?_⟩
      simp_all
  · rintro ⟨t, ht⟩
    refine ⟨(c :: t.data).asString, ?_⟩
    simpa

def mangleSuffix (b : Bool) (n : Name) : String :=
  match n with
  | .anonymous => ""
  | .str n s' =>
    let m := s'.mangle
    (if b ∨ checkDisambiguation m m.startValidPos then "_00" else "_") ++ m ++
      mangleSuffix (tailUnderscore s') n
  | .num n i => "_" ++ i.repr ++ "_" ++ mangleSuffix false n

@[simp]
theorem mangleSuffix_eq_empty_iff : mangleSuffix b n = "" ↔ n = anonymous := by
  cases n
  · simp [mangleSuffix]
  · rw [mangleSuffix]
    split <;> simp
  · simp [mangleSuffix]

@[simp]
theorem exists_mangleSuffix_eq_append (h : n ≠ anonymous) :
    ∃ s, mangleSuffix b n = "_" ++ s := by
  cases n
  · contradiction
  · rw [mangleSuffix]
    split
    · rw [show "_00" = "_" ++ "00" by rfl, String.append_assoc, String.append_assoc]
      simp
    · simp [String.append_assoc]
  · simp [mangleSuffix, String.append_assoc]

theorem of_mangle_eq_pushn {part : String} (h : part.mangle = "".pushn '_' ucount) :
    2 ∣ ucount ∧ part = "".pushn '_' (ucount / 2) := by
  obtain rfl | ⟨c, s, rfl⟩ := part.singleton_append_cases
  · simp_all
  · simp only [String.mangle_singleton_append, String.append_eq_pushn_empty_iff] at h
    obtain ⟨i, j, rfl, hc, hs⟩ := h
    revert hc
    fun_cases Char.mangle
    · intro; simp_all
    · intro h
      change (String.singleton '_').push '_' = _ at h
      simp only [String.push_eq_pushn_iff, String.singleton_eq_pushn_empty_iff,
        true_and, exists_eq_right, Nat.reduceAdd, eq_comm (a := 2)] at h
      suffices 2 ∣ j ∧ s = "".pushn '_' (j / 2) by
        simp [String.pushn_empty_succ, *, Nat.dvd_add_right]
      apply of_mangle_eq_pushn hs
    · rw [pushHex_eq_encodeHex (by decide)]
      simp [String.append_eq_pushn_empty_iff, List.eq_replicate_iff]
    · rw [pushHex_eq_encodeHex (by decide)]
      simp [String.append_eq_pushn_empty_iff, List.eq_replicate_iff]
    · rw [pushHex_eq_encodeHex (by decide)]
      simp [String.append_eq_pushn_empty_iff, List.eq_replicate_iff]
termination_by part.length

@[simp]
theorem checkDisambiguation_cast {s t : String} (h : s = t) {p : s.ValidPos} :
    checkDisambiguation t (p.cast h) = checkDisambiguation s p := by
  cases h; rfl

@[simp]
theorem checkDisambiguation_singleton_append (s t : String) :
    checkDisambiguation _ (String.posBetween s (String.singleton '_' ++ t)) =
      checkDisambiguation _ (String.posBetween (s.push '_') t) := by
  rw [checkDisambiguation]
  simp

@[simp]
theorem checkDisambiguation_singleton_append_of_isDigit {s t : String} {c : Char} (h : c.isDigit) :
    checkDisambiguation _ (String.posBetween s (String.singleton c ++ t)) = true := by
  simp only [Char.isDigit, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [checkDisambiguation]
  simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at h
  have (eq := hi) i := c.val.toNat - 48
  have hilt : i < 10 := by grind
  have hc : c = ⟨UInt32.ofNatLT (i + 48) (by clear hi h; grind), by clear hi h; grind [UInt32.toNat_ofNatLT]⟩ := by
    simp only [UInt32.ofNatLT_add, UInt32.reduceOfNatLT, Char.ext_iff, ← UInt32.toNat_inj,
      UInt32.toNat_add, UInt32.toNat_ofNatLT, UInt32.reduceToNat, Nat.reducePow, hi]
    rw [Nat.mod_eq_of_lt (by grind), Nat.sub_add_cancel h.1]
  clear hi
  have : c ≠ '_' ∧ c ≠ 'x' ∧ c ≠ 'u' ∧ c ≠ 'U' := by subst hc; clear h; decide +revert
  simp [this, UInt32.le_iff_toNat_le, h]

theorem checkDisambiguation_pushHex_x {s t : String} {n : UInt32} :
    checkDisambiguation _ (String.posBetween s ("x".pushHex 2 n ++ t)) = true := by
  rw [pushHex_eq_encodeHex (by decide), String.append_assoc]
  rw [checkDisambiguation]
  simp only [ne_eq, String.posBetween_eq_endValidPos_iff, String.append_eq_empty_iff,
    String.reduceEq, false_and, not_false_eq_true, ↓reduceDIte,
    String.get_posBetween_mk_cons_append, Char.reduceEq, ↓reduceIte,
    String.next_posBetween_mk_cons_append, String.reduceMk, checkLowerHex_cast]
  rw [String.empty_append, checkLowerHex_encodeHex]

theorem checkDisambiguation_pushHex_u {s t : String} {n : UInt32} :
    checkDisambiguation _ (String.posBetween s ("u".pushHex 4 n ++ t)) = true := by
  rw [pushHex_eq_encodeHex (by decide), String.append_assoc]
  rw [checkDisambiguation]
  simp only [ne_eq, String.posBetween_eq_endValidPos_iff, String.append_eq_empty_iff,
    String.reduceEq, false_and, not_false_eq_true, ↓reduceDIte,
    String.get_posBetween_mk_cons_append, Char.reduceEq, ↓reduceIte,
    String.next_posBetween_mk_cons_append, String.reduceMk, checkLowerHex_cast]
  rw [String.empty_append, checkLowerHex_encodeHex]

theorem checkDisambiguation_pushHex_U {s t : String} {n : UInt32} :
    checkDisambiguation _ (String.posBetween s ("U".pushHex 8 n ++ t)) = true := by
  rw [pushHex_eq_encodeHex (by decide), String.append_assoc]
  rw [checkDisambiguation]
  simp only [ne_eq, String.posBetween_eq_endValidPos_iff, String.append_eq_empty_iff,
    String.reduceEq, false_and, not_false_eq_true, ↓reduceDIte,
    String.get_posBetween_mk_cons_append, Char.reduceEq, ↓reduceIte,
    String.next_posBetween_mk_cons_append, String.reduceMk, checkLowerHex_cast]
  rw [String.empty_append, checkLowerHex_encodeHex]

theorem checkDisambiguation_pushHex__x {s t : String} {n : UInt32} :
    checkDisambiguation _ (String.posBetween s ("_x".pushHex 2 n ++ t)) = true := by
  rw [pushHex_eq_encodeHex (by decide), show "_x" = String.singleton '_' ++ "x" from rfl,
    String.append_assoc (s₁ := String.singleton _), ← pushHex_eq_encodeHex (by decide),
    String.append_assoc, checkDisambiguation_singleton_append, checkDisambiguation_pushHex_x]

theorem checkDisambiguation_pushHex__u {s t : String} {n : UInt32} :
    checkDisambiguation _ (String.posBetween s ("_u".pushHex 4 n ++ t)) = true := by
  rw [pushHex_eq_encodeHex (by decide), show "_u" = String.singleton '_' ++ "u" from rfl,
    String.append_assoc (s₁ := String.singleton _), ← pushHex_eq_encodeHex (by decide),
    String.append_assoc, checkDisambiguation_singleton_append, checkDisambiguation_pushHex_u]

theorem checkDisambiguation_pushHex__U {s t : String} {n : UInt32} :
    checkDisambiguation _ (String.posBetween s ("_U".pushHex 8 n ++ t)) = true := by
  rw [pushHex_eq_encodeHex (by decide), show "_U" = String.singleton '_' ++ "U" from rfl,
    String.append_assoc (s₁ := String.singleton _), ← pushHex_eq_encodeHex (by decide),
    String.append_assoc, checkDisambiguation_singleton_append, checkDisambiguation_pushHex_U]

theorem _root_.Nat.repr_ne_pushn : Nat.repr n ≠ String.pushn "" '_' k := by
  rw [Nat.repr, ne_eq, ← String.data_inj]
  simp only [List.data_asString, String.data_pushn, String.data_empty, List.nil_append]
  rw [Nat.toDigits, Nat.toDigitsCore]
  split
  · generalize hi : n % 10 = i
    have : i < 10 := hi ▸ Nat.mod_lt _ (by decide)
    simp only [List.eq_replicate_iff, List.length_cons, List.length_nil, Nat.zero_add,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq, not_and]
    intro; clear hi; decide +revert
  · rw [Nat.toDigitsCore_normalize]
    simp only [List.append_eq_replicate_iff, List.length_cons, List.length_nil,
      Nat.zero_add, List.replicate_one, List.cons.injEq, and_true, not_and]
    intro; intro
    generalize hi : n % 10 = i
    have : i < 10 := hi ▸ Nat.mod_lt _ (by decide)
    clear hi; revert i; decide

@[simp]
theorem charMangle_append_eq_uu_append_iff :
    Char.mangle c ++ s = .singleton '_' ++ (.singleton '_' ++ t) ↔ c = '_' ∧ s = t := by
  fun_cases Char.mangle
  · constructor <;> intro <;> simp_all
  · rw [show "__" = .singleton '_' ++ .singleton '_' by rfl, String.append_assoc]
    simp_all
  · rw [pushHex_eq_encodeHex (by decide), show "_x" = .singleton '_' ++ .singleton 'x' by rfl,
      String.append_assoc, String.append_assoc]
    simp [*]
  · rw [pushHex_eq_encodeHex (by decide), show "_u" = .singleton '_' ++ .singleton 'u' by rfl,
      String.append_assoc, String.append_assoc]
    simp [*]
  · rw [pushHex_eq_encodeHex (by decide), show "_U" = .singleton '_' ++ .singleton 'U' by rfl,
      String.append_assoc, String.append_assoc]
    simp [*]

theorem of_charMangle_append_eq_not_u_append (h : a ≠ '_')
    (h' : Char.mangle c ++ s = .singleton a ++ t) :
    c = a ∧ c.mangle = .singleton a := by
  revert h'
  fun_cases Char.mangle
  · simp [imp.swap (b := s = t)]
  · rw [show "__" = .singleton '_' ++ .singleton '_' by rfl, String.append_assoc]
    simp [h.symm]
  · rw [pushHex_eq_encodeHex (by decide), show "_x" = .singleton '_' ++ .singleton 'x' by rfl,
      String.append_assoc, String.append_assoc]
    simp [h.symm]
  · rw [pushHex_eq_encodeHex (by decide), show "_u" = .singleton '_' ++ .singleton 'u' by rfl,
      String.append_assoc, String.append_assoc]
    simp [h.symm]
  · rw [pushHex_eq_encodeHex (by decide), show "_U" = .singleton '_' ++ .singleton 'U' by rfl,
      String.append_assoc, String.append_assoc]
    simp [h.symm]

theorem of_mangle_append_mangleSuffix_eq_pushn {b : Bool} {nm : Name}
    (h : part.mangle ++ mangleSuffix b nm = "".pushn '_' ucount) :
    2 ∣ ucount ∧ part = "".pushn '_' (ucount / 2) ∧ nm = .anonymous := by
  revert h
  fun_cases mangleSuffix
  · intro h
    simp only [String.append_empty] at h
    simp only [and_true]
    exact of_mangle_eq_pushn h
  · split
    · simp only [String.append_eq_pushn_empty_iff, reduceCtorEq, and_false, imp_false, not_exists,
        not_and]
      rintro - - rfl - - - rfl ⟨j, -, rfl, h, -⟩
      exfalso; revert h
      change ¬"_0".push '0' = _
      cases j <;> simp [String.pushn_succ]
    · simp only [String.append_eq_pushn_empty_iff, reduceCtorEq, and_false,
        imp_false, not_exists, not_and]
      rintro - - rfl - - - rfl ⟨-, j, rfl, -, h⟩ -
      rename_i h'
      simp only [not_or, Bool.not_eq_true] at h'
      rw [h] at h'
      rw [String.startValidPos_eq_posBetween', checkDisambiguation_cast] at h'
      replace h' := h'.2; revert h'; clear h; rw [imp_false, Bool.not_eq_false]
      have (eq := seq) s := ""
      rw (occs := [1, 3]) [← seq]; clear seq
      induction j generalizing s with
      | zero =>
        rw [checkDisambiguation, dif_neg]
        · rw [ne_eq, String.posBetween_eq_endValidPos_iff, String.pushn_zero]
          simp only [not_true_eq_false, not_false_eq_true]
      | succ k ih => rw [String.pushn_empty_succ, checkDisambiguation_singleton_append, ih]
  · intro h
    simp only [String.append_eq_pushn_empty_iff, String.mk_eq_pushn_empty_iff] at h
    exfalso
    obtain ⟨-, -, rfl, -, -, -, rfl, ⟨-, -, rfl, ⟨-, l, rfl, -, h''⟩, -⟩, -⟩ := h
    exact Nat.repr_ne_pushn h''

theorem checkDisambiguation_of_mangle_append_eq (hc : c ≠ '_')
    (h : Char.mangle c ++ s = .singleton '_' ++ t) :
    checkDisambiguation _ (String.posBetween sl (Char.mangle c ++ sr)) := by
  revert h
  fun_cases Char.mangle
  · simp_all
  · contradiction
  · simp [checkDisambiguation_pushHex__x]
  · simp [checkDisambiguation_pushHex__u]
  · simp [checkDisambiguation_pushHex__U]

theorem checkDisambiguation_of_mangle_append_eq' (hc : c ≠ '_')
    (h : Char.mangle c ++ s = .singleton '_' ++ t) :
    checkDisambiguation _ (String.posBetween sl t) := by
  revert h
  fun_cases Char.mangle
  · simp_all
  · contradiction
  · rw [pushHex_eq_encodeHex (by decide), show "_x" = .singleton '_' ++ "x" by rfl,
      String.append_assoc, String.append_assoc, ← @String.append_assoc "x",
      ← pushHex_eq_encodeHex (by decide), String.append_right_inj]
    rintro rfl; rw [checkDisambiguation_pushHex_x]
  · rw [pushHex_eq_encodeHex (by decide), show "_u" = .singleton '_' ++ "u" by rfl,
      String.append_assoc, String.append_assoc, ← @String.append_assoc "u",
      ← pushHex_eq_encodeHex (by decide), String.append_right_inj]
    rintro rfl; rw [checkDisambiguation_pushHex_u]
  · rw [pushHex_eq_encodeHex (by decide), show "_U" = .singleton '_' ++ "U" by rfl,
      String.append_assoc, String.append_assoc, ← @String.append_assoc "U",
      ← pushHex_eq_encodeHex (by decide), String.append_right_inj]
    rintro rfl; rw [checkDisambiguation_pushHex_U]

theorem mangleSuffix_ne_append (hc : c ≠ '_') :
    mangleSuffix b nm ≠ "".pushn '_' (2 * ucount) ++ (String.singleton c ++ t) := by
  induction nm generalizing b ucount
  · simp [mangleSuffix]
  · rename_i n s ih
    rw [mangleSuffix]
    split
    · rw [show "_00" = .singleton '_' ++ .singleton '0' ++ "0" by rfl,
        String.append_assoc, String.append_assoc, String.append_assoc]
      rcases ucount with _ | u
      · simp [hc.symm]
      · simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc]
    · rename_i h; simp only [not_or, Bool.not_eq_true] at h; replace h := h.2
      rw [show "_" = .singleton '_' by rfl]
      rcases ucount with _ | u
      · simp [String.append_assoc, hc.symm]
      simp only [String.append_assoc, Nat.mul_add, Nat.mul_one, String.pushn_empty_succ, ne_eq,
        String.append_right_inj]
      rw [String.startValidPos_eq_posBetween', checkDisambiguation_cast] at h
      have (eq := aaeq) aa := ""; rw [← aaeq] at h; clear aaeq
      generalize tailUnderscore s = b
      induction u generalizing s aa with
      | zero =>
        obtain rfl | ⟨d, s, rfl⟩ := s.singleton_append_cases
        · simp [checkDisambiguation] at h
        simp only [String.mangle_singleton_append, Nat.mul_zero, String.pushn_zero,
          String.empty_append, ne_eq]
        by_cases hd : d = '_'
        · simp [hd, String.append_assoc, -String.append_singleton, hc.symm]
        · intro h'
          rw [String.append_assoc] at h'
          rw [String.mangle_singleton_append, checkDisambiguation_of_mangle_append_eq hd h'] at h
          contradiction
      | succ u ih' =>
        simp only [String.append_assoc, Nat.mul_add, Nat.mul_one, String.pushn_empty_succ]
        obtain rfl | ⟨d, s, rfl⟩ := s.singleton_append_cases
        · simp [checkDisambiguation] at h
        · simp only [String.mangle_singleton_append, String.append_assoc,
            charMangle_append_eq_uu_append_iff, not_and]
          rintro rfl
          rw [String.mangle_singleton_append, Char.mangle_u, String.append_assoc,
            checkDisambiguation_singleton_append, checkDisambiguation_singleton_append] at h
          exact ih' _ _ h
  · rename_i n i ih
    rw [mangleSuffix, show "_" = .singleton '_' by rfl, String.append_assoc, String.append_assoc]
    rcases ucount with _ | u
    · simp [hc.symm]
    · obtain ⟨_ | ⟨d, ds⟩, ⟨hds, -⟩, hrepr, -⟩ := Nat.exists_repr_eq i
      · contradiction
      rw [← hrepr, digitsToString, String.append_assoc]
      simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc]

@[simp]
theorem imp_imp_imp (a b c : Prop) :
    (a → b) → (a → c) ↔ a → b → c := by
  grind

theorem checkLowerHex_append_mangleSuffix_imp
    (h : checkLowerHex n _ (String.posBetween s t) = false) :
    checkLowerHex n _ (String.posBetween s' (t ++ mangleSuffix b nm)) = false := by
  induction n generalizing s s' t with
  | zero => simp [checkLowerHex] at h
  | succ k ih =>
    obtain rfl | ⟨c, s, rfl⟩ := t.singleton_append_cases
    · simp only [checkLowerHex, String.posBetween_eq_endValidPos_iff, String.empty_append,
        mangleSuffix_eq_empty_iff, ge_iff_le, dite_eq_left_iff, Bool.and_eq_false_imp,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      intro hnm
      obtain ⟨s, hs⟩ := exists_mangleSuffix_eq_append (b := b) hnm
      simp [String.posBetween_congr rfl (String.empty_append.trans hs)]
    · rw [String.append_assoc]
      revert h
      simp [checkLowerHex, eq_true ih]

theorem of_mangle_append_mangleSuffix_eq_pushn_even_append (htc : tc ≠ '_')
    (hb : tailUnderscore ss → b = true)
    (ht : ss.mangle ++ mangleSuffix b nm =
        "".pushn '_' (2 * u) ++ (String.singleton tc ++ t'))
    (hdis : checkDisambiguation _ (String.posBetween sl ss.mangle) = false) :
    tc.isDigit = false ∧ ¬(tc = 'x' ∧ checkLowerHex 2 _ (String.posBetween sll t')) ∧
      ¬(tc = 'u' ∧ checkLowerHex 4 _ (String.posBetween sll t')) ∧
      ¬(tc = 'U' ∧ checkLowerHex 8 _ (String.posBetween sll t')) := by
  obtain rfl | ⟨c, s, rfl⟩ := ss.singleton_append_cases
  · simp only [String.mangle_empty, String.empty_append] at ht
    exact absurd ht (mangleSuffix_ne_append htc)
  · simp only [String.mangle_singleton_append] at ht
    cases u with
    | succ u =>
      simp only [String.append_assoc, Nat.mul_add, Nat.mul_one, String.pushn_empty_succ,
        charMangle_append_eq_uu_append_iff] at ht
      rw [ht.1, String.mangle_singleton_append, Char.mangle_u, String.append_assoc,
        checkDisambiguation_singleton_append, checkDisambiguation_singleton_append] at hdis
      apply of_mangle_append_mangleSuffix_eq_pushn_even_append htc _ ht.2 hdis
      intro h
      apply hb
      simp only [tailUnderscore_def] at h ⊢
      obtain ⟨t, rfl⟩ := h
      exact ⟨String.singleton c ++ t, String.append_push _⟩
    | zero => ?_
    simp only [Nat.mul_zero, String.pushn_zero, String.empty_append, String.append_assoc] at ht
    obtain ⟨rfl, hm⟩ := of_charMangle_append_eq_not_u_append htc ht
    rw [String.mangle_singleton_append, hm] at hdis
    rw [checkDisambiguation] at hdis
    replace hdis : if c = 'x' then checkLowerHex 2 _ ((sl.push c).posBetween s.mangle) = false
        else if c = 'u' then checkLowerHex 4 _ ((sl.push c).posBetween s.mangle) = false
        else if c = 'U' then checkLowerHex 8 _ ((sl.push c).posBetween s.mangle) = false
        else c.isDigit = false := by simpa [htc, Char.isDigit] using hdis
    rw [hm, String.append_right_inj] at ht
    rw [← ht]
    split at hdis
    · simp [checkLowerHex_append_mangleSuffix_imp hdis, *]
    split at hdis
    · simp [checkLowerHex_append_mangleSuffix_imp hdis, *]
    split at hdis
    · simp [checkLowerHex_append_mangleSuffix_imp hdis, *]
    · simp [*]

theorem unmangleAux_ucount_reduction (hc : c ≠ '_')
    (h : part.mangle ++ mangleSuffix (b || tailUnderscore part) nm =
      "".pushn '_' (2 * ucount) ++ (String.singleton c ++ t)) :
    ∃ p2 : String, ∃ b, p2.mangle ++ mangleSuffix (b || tailUnderscore p2) nm = t ∧
      part = "".pushn '_' ucount ++ (String.singleton c ++ p2) := by
  induction ucount generalizing part b with
  | zero =>
    obtain rfl | ⟨d, s, rfl⟩ := part.singleton_append_cases
    · simp only [String.mangle_empty, tailUnderscore_empty, Bool.or_false, String.empty_append] at h
      apply absurd h
      exact mangleSuffix_ne_append hc
    · simp only [String.mangle_singleton_append, String.append_assoc, Nat.mul_zero,
        String.pushn_zero, String.empty_append] at h
      obtain ⟨rfl, h'⟩ := of_charMangle_append_eq_not_u_append hc h
      simp only [h', String.append_right_inj] at h
      exists s, b || tailUnderscore (String.singleton d ++ s)
      simp only [String.pushn_zero, String.empty_append, and_true]
      refine cast ?_ h; congr 3
      simp only [Bool.eq_self_or, Bool.or_eq_true, tailUnderscore_def]
      rintro ⟨t, rfl⟩
      exact .inr ⟨String.singleton d ++ t, String.append_push _⟩
  | succ k ih =>
    obtain rfl | ⟨d, s, rfl⟩ := part.singleton_append_cases
    · simp only [String.mangle_empty, tailUnderscore_empty, Bool.or_false, String.empty_append] at h
      apply absurd h
      exact mangleSuffix_ne_append hc
    · simp only [String.mangle_singleton_append, String.append_assoc, Nat.mul_add,
        Nat.mul_one, String.pushn_empty_succ, charMangle_append_eq_uu_append_iff] at h ih
      have ⟨p2, b, hp2, hsp2⟩ := @ih (b || tailUnderscore (String.singleton d ++ s)) s ?side
      case side =>
        refine cast ?_ h.2; congr 3
        simp only [Bool.eq_self_or, Bool.or_eq_true, tailUnderscore_def]
        rintro ⟨t, rfl⟩
        exact .inr ⟨String.singleton d ++ t, String.append_push _⟩
      exists p2, b
      refine ⟨hp2, ?_⟩
      rw [hsp2, String.pushn_empty_succ, h.1, String.append_assoc]

theorem unmangleAux_nameStart_normal_str {s s' t : String} {n res : Name}
    (ht : t = s'.mangle ++ mangleSuffix (tailUnderscore s') n)
    (h : checkDisambiguation s'.mangle s'.mangle.startValidPos = false)
    (unmangleAux_thm : ∀ part nm {acc ucount ss tt}, 2 * tt.length + ucount < 2 * t.length →
      part.mangle ++ mangleSuffix (tailUnderscore part) nm = "".pushn '_' ucount ++ tt →
      unmangleAux (ss ++ tt) (ss.posBetween tt) res acc ucount = str res (acc ++ part) +-+! nm) :
    unmangleAux.nameStart _ (s.posBetween t) res = str res s' +-+! n := by
  generalize hm : s'.mangle = m at h ht
  obtain rfl | ⟨c, s, rfl⟩ := s'.singleton_append_cases
  · simp only [String.mangle_empty] at hm
    subst hm
    simp [checkDisambiguation] at h
  subst ht
  simp only [String.mangle_singleton_append] at hm
  subst hm
  generalize hc : c.mangle = m at h
  revert hc
  rw [String.startValidPos_eq_posBetween', checkDisambiguation_cast] at h
  rw [String.append_assoc]
  fun_cases Char.mangle
  · rintro rfl
    rw [unmangleAux.nameStart, dif_neg (by simp)]
    simp only [String.get_posBetween_singleton_append,
      String.next_posBetween_singleton_append, String.ValidPos.get_cast, ne_eq,
      String.ValidPos.cast_eq_endValidPos, String.posBetween_eq_endValidPos_iff,
      String.ValidPos.next_cast, unmangleAux_cast, unmangleAux_decodeNum_cast]
    split
    · simp [checkDisambiguation_singleton_append_of_isDigit ‹_›] at h
    split
    · simp_all
    · rw [unmangleAux_thm s n]
      · simp
      · simp only [String.pushn_zero, String.empty_append, String.append_right_inj]
        congr 1
        rw [tailUnderscore_singleton_append ‹_›]
  · rintro rfl
    rw [unmangleAux.nameStart, dif_neg (by simp)]
    simp only [String.get_posBetween_mk_cons_append, Char.reduceIsDigit,
      Bool.false_eq_true, ↓reduceIte, String.next_posBetween_mk_cons_append, String.reduceMk,
      unmangleAux_cast]
    rw [unmangleAux_thm (String.singleton '_' ++ s) n, String.empty_append, ‹c = '_'›]
    · simp +arith [*, String.length_mk, Char.mangle]
    · simp [Char.mangle, show "__" = String.singleton '_' ++ "_" by rfl, String.append_assoc,
        ‹c = '_'›]
  · rintro rfl
    simp only [checkDisambiguation_pushHex__x, Bool.true_eq_false] at h
  · rintro rfl
    simp only [checkDisambiguation_pushHex__u, Bool.true_eq_false] at h
  · rintro rfl
    simp only [checkDisambiguation_pushHex__U, Bool.true_eq_false] at h

/-macro_rules
  | `(tactic| induction $[using $t]? $[generalizing $g*]? $(alts?)?) =>
    `(tactic| induction $(⟨#[]⟩):elimTarget,* $[using $t:term]? $[generalizing $g*]? $(alts?)?)-/

@[simp]
theorem tailUnderscore_or (b : Bool) (pc : Char) (pt : String) :
    (b || tailUnderscore (String.singleton pc ++ pt) || tailUnderscore pt) =
      (b || tailUnderscore (String.singleton pc ++ pt)) := by
  simp only [Bool.or_eq_left_iff_imp, Bool.or_eq_true, tailUnderscore_def]
  rintro ⟨t, rfl⟩
  exact .inr ⟨String.singleton pc ++ t, String.append_push _⟩

/-
t s : String
res : Name
acc : String
nm : Name
b : Bool
tc : Char
t' : String
htc : t = String.singleton tc ++ t'
htc1 : ¬tc = '_'
pc : Char
pt : String
h✝¹ : ¬(pc.isAlpha || pc.isDigit) = true
h✝ : pc = '_'
u : Nat
hu : (2 * (u + 1) + 1) % 2 = 1
h : pt.mangle ++ mangleSuffix (b || tailUnderscore (String.singleton pc ++ pt)) nm =
  "".pushn '_' (2 * u + 1) ++ (String.singleton tc ++ t')
⊢ Lean.Name.unmangleAux✝ (s ++ (String.singleton tc ++ t')) (s.posBetween (String.singleton tc ++ t')) res acc
    (2 * u + 2 + 1) =
  res.str (acc ++ (String.singleton pc ++ pt)) +-+! nm
-/

theorem checkDisambiguation_of_mangle_append_mangleSuffix_eq
    (h : pt.mangle ++ mangleSuffix b nm =
      "".pushn '_' (2 * u + 1) ++ t)
    (hb : tailUnderscore ("_" ++ pt) → b)
    (htc : tc ≠ '_')
    (ht : t = String.singleton tc ++ tt) :
    checkDisambiguation _ (String.posBetween sl t) := by
  obtain rfl | ⟨c, pt, rfl⟩ := pt.singleton_append_cases
  · simp only [String.append_empty, tailUnderscore_u, forall_const] at hb
    simp only [String.mangle_empty, hb, String.empty_append] at h
    rcases nm with _ | _ | ⟨_, i⟩
    · simp [mangleSuffix] at h
    · simp only [mangleSuffix, true_or, ↓reduceIte,
        show "_00" = .singleton '_' ++ (.singleton '0' ++ "0") by rfl, String.append_assoc,
        String.pushn_empty_succ, String.append_right_inj] at h
      cases u with
      | succ u => simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc] at h
      | zero => ?_
      simp only [Nat.mul_zero, String.pushn_zero, String.empty_append] at h
      cases h
      exact checkDisambiguation_singleton_append_of_isDigit (by decide)
    · simp only [mangleSuffix, show "_" = .singleton '_' by rfl, String.append_assoc,
        String.pushn_empty_succ, String.append_right_inj] at h
      obtain ⟨_ | ⟨d, l⟩, ⟨hds, -⟩, hrepr, -⟩ := i.exists_repr_eq
      · contradiction
      rw [← hrepr, digitsToString] at h
      cases u with
      | succ u => simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc] at h
      | zero => ?_
      simp only [String.append_assoc, Nat.mul_zero, String.pushn_zero, String.empty_append] at h
      cases h
      exact checkDisambiguation_singleton_append_of_isDigit (by simp)
  · simp only [String.mangle_singleton_append, String.append_assoc] at h
    by_cases hc : c = '_'
    · simp only [hc, Char.mangle_u, String.append_assoc, String.pushn_empty_succ,
        String.append_right_inj] at h
      rcases hu : u with _ | u
      · simp [hu, ht, htc.symm] at h
      · rw [hu, Nat.mul_add, String.pushn_empty_succ, String.append_assoc,
          String.append_right_inj] at h
        apply checkDisambiguation_of_mangle_append_mangleSuffix_eq h _ htc ht
        intro h₁
        apply hb
        rw [tailUnderscore_def] at h₁ ⊢
        obtain ⟨t, ht⟩ := h₁
        exists "_" ++ t
        simp [hc, show .singleton '_' = "_" by rfl, ht, String.append_push]
    · rw [String.pushn_empty_succ, String.append_assoc] at h
      rcases u with _ | u
      · simp only [Nat.mul_zero, String.pushn_zero, String.empty_append] at h
        rw [checkDisambiguation_of_mangle_append_eq' hc h]
      · simp [hc, Nat.mul_add, String.pushn_empty_succ, String.append_assoc] at h
termination_by u

theorem unmangleAux_ucount_output (hc : c ≠ '_')
    (h : pt.mangle ++ mangleSuffix (b || tailUnderscore ("_" ++ pt)) nm =
      "".pushn '_' (2 * u + 1) ++ (String.singleton c ++ t)) :
    unmangleAux _ (String.posBetween s (String.singleton c ++ t)) res acc (2 * u + 3) =
      unmangleAux _ (String.posBetween s (String.singleton c ++ t)) res (acc.push '_') (2 * u + 1) := by
  fun_cases Lean.Name.unmangleAux _ _ _ acc _
  · rw [unmangleAux, dif_pos ‹_›]
    simp [Nat.mul_add_div, String.pushn_succ']
  · rename_i ch _ hch
    simp [hc, ch] at hch
  · simp_all
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg (by simp), if_pos ‹_›, dif_pos ‹_›]
    rename_i p _ _ _ res _
    simp [res, p, Nat.mul_add_div, String.pushn_succ']
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg (by simp), if_pos ‹_›, dif_neg ‹_›]
    rename_i ch p _ _ _ res _
    simp [res, p, ch, Nat.mul_add_div, String.pushn_succ']
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg (by simp), if_neg ‹_›, dif_pos ‹_›]
    rename_i ch p _ _ _ _ acc
    simp [acc, p, Nat.mul_add_div, String.pushn_succ']
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg (by simp), if_neg ‹_›,
      dif_neg ‹_›, dif_pos ‹_›]
    rename_i ch p _ _ _ _ _ acc
    simp [acc, p, Nat.mul_add_div, String.pushn_succ']
  · conv => rhs; rw [unmangleAux, dif_neg ‹_›, if_neg ‹_›, if_neg (by simp), if_neg ‹_›,
      dif_neg ‹_›, dif_neg ‹_›, dif_pos ‹_›]
    rename_i ch p _ _ _ _ _ _ acc
    simp [acc, p, Nat.mul_add_div, String.pushn_succ']
  · exfalso
    replace h := checkDisambiguation_of_mangle_append_mangleSuffix_eq (sl := s) h (by simpa using Or.inr) hc rfl
    rename_i ch p hu _ hds h_x h_u h_U
    simp only [String.get_posBetween_singleton_append, ↓Char.isValue, Bool.not_eq_true,
      String.next_posBetween_singleton_append, checkLowerHex_cast, not_and, ch, p]
      at hu hds h_x h_u h_U
    rw [Bool.eq_false_iff, ne_eq, Char.isDigit, ← Bool.decide_and, decide_eq_true_eq, ge_iff_le] at hds
    rw [checkDisambiguation] at h
    simp +contextual [hu, h_x, h_u, h_U, hds] at h

mutual

theorem unmangleAux_thm (part nm b)
    (ht : part.mangle ++ mangleSuffix (b || tailUnderscore part) nm = "".pushn '_' ucount ++ t) :
    unmangleAux (s ++ t) (s.posBetween t) res acc ucount = str res (acc ++ part) +-+! nm := by
  obtain rfl | ⟨tc, t', htc⟩ := t.singleton_append_cases
  · rw [unmangleAux]
    simp only [String.posBetween_eq_endValidPos_iff, ↓reduceDIte]
    rw [String.append_empty] at ht
    obtain ⟨hdvd, rfl, rfl⟩ := of_mangle_append_mangleSuffix_eq_pushn ht
    rw [← String.pushn_normalize, extendRev]
  by_cases htc1 : tc = '_'
  · rw [htc, htc1, unmangleAux]
    simp only [String.posBetween_eq_endValidPos_iff, String.append_eq_empty_iff,
      String.singleton_ne_empty, false_and, ↓reduceDIte, String.get_posBetween_singleton_append,
      ↓reduceIte, String.next_posBetween_singleton_append, unmangleAux_cast]
    apply unmangleAux_thm
    rw [String.pushn_succ, String.push_append]
    rwa [htc, htc1] at ht
  by_cases hu : 2 ∣ ucount
  · obtain ⟨ucount, rfl⟩ := hu
    rw [htc]
    suffices unmangleAux (s.push tc ++ t') ((s.push tc).posBetween t') res ((acc.pushn '_' ucount).push tc) 0 =
        res.str (acc ++ part) +-+! nm by as_aux_lemma => rw [unmangleAux]; simpa [htc1]
    rw [htc] at ht
    obtain ⟨p2, b, hb, hpart⟩ := unmangleAux_ucount_reduction htc1 ht
    rw [unmangleAux_thm p2 nm b (by simpa), hpart, ← String.append_assoc, ← String.pushn_normalize,
      String.push_append]
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mod_two_not_eq_zero] at hu
  rcases (⟨ucount / 2, hu ▸ Nat.div_add_mod ucount 2⟩ : ∃ u, 2 * u + 1 = ucount) with ⟨u, hu⟩
  rw [← hu] at ht ⊢
  obtain rfl | ⟨pc, pt, rfl⟩ := part.singleton_append_cases
  · simp only [String.mangle_empty, tailUnderscore_empty, Bool.or_false, String.empty_append,
      htc, String.pushn_empty_succ, String.append_assoc] at ht
    rcases nm with _ | ⟨nm, ss⟩ | ⟨nm, ii⟩
    · simp [mangleSuffix] at ht
    · rw [mangleSuffix] at ht
      split at ht
      · rw [show "_00" = .singleton '_' ++ .singleton '0' ++ "0" by rfl,
          String.append_assoc, String.append_assoc, String.append_assoc,
          String.append_right_inj] at ht
        cases u with
        | succ u => simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc] at ht
        | zero => ?_
        simp only [Nat.mul_zero, String.pushn_zero, String.empty_append,
          String.singleton_append_inj] at ht
        rw [htc, ← ht.1, ← ht.2]
        suffices unmangleAux _ (((s.push '0').push '0').posBetween ("" ++ (ss.mangle ++ mangleSuffix (tailUnderscore ss) nm)))
            (res.str acc) "" 0 = (res.str acc).str ss +-+! nm by
          as_aux_lemma => rw [unmangleAux]; simpa
        have : ss.mangle.length + (mangleSuffix (tailUnderscore ss) nm).length < t.length := by
          simp +arith [htc, ← ht.2]
        rw [String.empty_append, unmangleAux_thm ss nm false, String.empty_append]
        simp
      · rename_i hdis; simp only [not_or, Bool.not_eq_true] at hdis; replace hdis := hdis.2
        rw [show "_" = .singleton '_' by rfl, String.append_assoc, String.append_right_inj] at ht
        rw [String.startValidPos_eq_posBetween', checkDisambiguation_cast] at hdis
        have thing := of_mangle_append_mangleSuffix_eq_pushn_even_append htc1 id ht hdis (sll := s.push tc)
        rw [htc]
        suffices unmangleAux (s.push tc ++ t') ((s.push tc).posBetween t') (res.str acc)
            (("".pushn '_' ((2 * u + 1) / 2)).push tc) 0 = (res.str acc).str ss +-+! nm by
          as_aux_lemma => rw [unmangleAux]; simpa [htc1, thing]
        simp only [Nat.zero_lt_succ, Nat.mul_add_div, Nat.reduceDiv, Nat.add_zero]
        obtain ⟨p2, b, hb, hpart⟩ := unmangleAux_ucount_reduction (b := false) htc1 ht
        rw [unmangleAux_thm p2 nm b (by simpa), hpart, ← String.append_assoc,
          String.push_append, String.append_assoc]
    · rw [mangleSuffix, show "_" = .singleton '_' from rfl, String.append_assoc,
        String.append_assoc, String.append_right_inj] at ht
      obtain ⟨_ | ⟨d, ds⟩, ⟨hds, hds'⟩, hrepr, hdsval⟩ := Nat.exists_repr_eq ii
      · contradiction
      rw [← hrepr, digitsToString, String.append_assoc] at ht
      cases u with
      | succ => simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc] at ht
      | zero => ?_
      simp only [List.head?_cons, Fin.isValue, Option.some.injEq, List.cons.injEq] at hds'
      simp only [Nat.mul_zero, String.pushn_zero, String.empty_append,
        String.singleton_append_inj] at ht
      cases ht.1
      simp only [Nat.mul_zero, Nat.zero_add, String.append_empty, extendRev]
      rw [htc]
      have thing : ¬(d = 0 ∧ ∃ h : t' ≠ "", ((s.push (adigit d)).posBetween t').get (by simpa) = '0') := by
        rw [not_and]; rintro rfl; cases (hds' rfl).2
        simp only [digitsToString, String.empty_append, true_and] at ht
        simp [String.posBetween_congr rfl ht.symm]
      suffices unmangleAux.decodeNum (s.push (adigit d) ++ t') ((s.push (adigit d)).posBetween t') (res.str acc) ↑d =
          (res.str acc).num ii +-+! nm by
        as_aux_lemma => rw [unmangleAux]; simpa [thing]
      rw [← hdsval, digitsToNat, Nat.zero_mul, Nat.zero_add, decodeNum_thm]
      exact ht.2.symm
  · simp only [String.mangle_singleton_append, String.pushn_empty_succ, String.append_assoc] at ht
    revert ht
    fun_cases Char.mangle pc
    · simp only [String.singleton_append_inj, and_imp]
      rintro rfl; simp at *
    · rw [show "__" = .singleton '_' ++ .singleton '_' by rfl, String.append_assoc, htc,
        String.append_right_inj]
      rcases u with _ | u
      · simp [Ne.symm htc1]
      · simp only [Nat.mul_add, Nat.mul_one, String.pushn_empty_succ (n := 2 * u + 1),
          String.append_assoc, String.append_right_inj]
        intro h
        rw [‹pc = _›] at h
        rw [unmangleAux_ucount_output htc1 h]
        have : 2 * (1 + t'.length) + (2 * u + 1) < 2 * t.length + ucount := by
          simp +arith [← hu, htc]
        rw [unmangleAux_thm pt nm (b || tailUnderscore (String.singleton '_' ++ pt)), ‹pc = _›,
          String.push_append]
        simp [h]
    · rw [pushHex_eq_encodeHex (by decide), show "_x" = .singleton '_' ++ .singleton 'x' by rfl,
        String.append_assoc, String.append_assoc, String.append_right_inj]
      cases u with
      | succ u => simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc]
      | zero => ?_
      simp only [Nat.mul_zero, String.pushn_zero, String.empty_append, Nat.zero_add]
      intro ht; rw [← ht]
      suffices unmangleAux _
          ((s.push 'x' ++ encodeHex 2 pc.val.toNat).posBetween
            (pt.mangle ++ mangleSuffix (b || tailUnderscore (String.singleton pc ++ pt)) nm))
          res (acc.push (Char.ofNat (pc.val.toNat % 256))) 0 =
          res.str (acc ++ (String.singleton pc ++ pt)) +-+! nm by
        as_aux_lemma => rw [unmangleAux]; simpa [checkLowerHex_encodeHex, parseLowerHex_encodeHex, encodeHex_thing,
          String.push_append]
      have : pt.mangle.length + (mangleSuffix (b || tailUnderscore (String.singleton pc ++ pt)) nm).length < t.length := by
        simp +arith [← ht]
      rw [Nat.mod_eq_of_lt ‹_›, ← Char.toNat, Char.ofNat_toNat,
        unmangleAux_thm pt nm (b || tailUnderscore (String.singleton pc ++ pt)), String.push_append]
      simp
    · rw [pushHex_eq_encodeHex (by decide), show "_u" = .singleton '_' ++ .singleton 'u' by rfl,
        String.append_assoc, String.append_assoc, String.append_right_inj]
      cases u with
      | succ u => simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc]
      | zero => ?_
      simp only [Nat.mul_zero, String.pushn_zero, String.empty_append, Nat.zero_add]
      intro ht; rw [← ht]
      suffices unmangleAux _
          ((s.push 'u' ++ encodeHex 4 pc.val.toNat).posBetween
            (pt.mangle ++ mangleSuffix (b || tailUnderscore (String.singleton pc ++ pt)) nm))
          res (acc.push (Char.ofNat (pc.val.toNat % 65536))) 0 =
          res.str (acc ++ (String.singleton pc ++ pt)) +-+! nm by
        as_aux_lemma => rw [unmangleAux]; simpa [checkLowerHex_encodeHex, parseLowerHex_encodeHex, encodeHex_thing,
          String.push_append]
      have : pt.mangle.length + (mangleSuffix (b || tailUnderscore (String.singleton pc ++ pt)) nm).length < t.length := by
        simp +arith [← ht]
      rw [Nat.mod_eq_of_lt ‹_›, ← Char.toNat, Char.ofNat_toNat,
        unmangleAux_thm pt nm (b || tailUnderscore (String.singleton pc ++ pt)), String.push_append]
      simp
    · rw [pushHex_eq_encodeHex (by decide), show "_U" = .singleton '_' ++ .singleton 'U' by rfl,
        String.append_assoc, String.append_assoc, String.append_right_inj]
      cases u with
      | succ u => simp [Nat.mul_add, String.pushn_empty_succ, String.append_assoc]
      | zero => ?_
      simp only [Nat.mul_zero, String.pushn_zero, String.empty_append, Nat.zero_add]
      intro ht; rw [← ht]
      suffices unmangleAux _
          ((s.push 'U' ++ encodeHex 8 pc.val.toNat).posBetween
            (pt.mangle ++ mangleSuffix (b || tailUnderscore (String.singleton pc ++ pt)) nm))
          res (acc.push (Char.ofNat pc.val.toNat)) 0 =
          res.str (acc ++ (String.singleton pc ++ pt)) +-+! nm by
        as_aux_lemma => rw [unmangleAux]; simpa [checkLowerHex_encodeHex, parseLowerHex_encodeHex, encodeHex_thing,
          String.push_append]
      have : pt.mangle.length + (mangleSuffix (b || tailUnderscore (String.singleton pc ++ pt)) nm).length < t.length := by
        simp +arith [← ht]
      rw [← Char.toNat, Char.ofNat_toNat,
        unmangleAux_thm pt nm (b || tailUnderscore (String.singleton pc ++ pt)), String.push_append]
      simp
termination_by 2 * t.length + ucount

theorem decodeNum_thm (h : t = digitsToString l ++ ("_" ++ mangleSuffix false nm)) :
    unmangleAux.decodeNum (s ++ t) (s.posBetween t) res acc =
      num res (digitsToNat l acc) +-+! nm := by
  subst h
  rcases hl_eq : l with _ | ⟨c, l⟩
  · rw [digitsToString, digitsToNat, String.empty_append]
    suffices (if h : nm = anonymous then res.num acc
        else
          unmangleAux.nameStart (s.push '_' ++ ("" ++ mangleSuffix false nm))
            (((s.push '_').posBetween ("" ++ mangleSuffix false nm)).next (by simpa)) (res.num acc)) =
        res.num acc +-+! nm by
      as_aux_lemma => rw [unmangleAux.decodeNum]; simpa [-String.String.mk_eq_asString]
    split
    · simp [*]
    · obtain ⟨t, ht⟩ := exists_mangleSuffix_eq_append (b := false) ‹_›
      conv => enter [1, 2, 1]; apply String.posBetween_congr rfl; rw [ht, String.empty_append]
      simp only [String.ValidPos.next_cast, String.next_posBetween_mk_cons_append,
        String.reduceMk, String.ValidPos.cast_cast, unmangleAux_nameStart_cast]
      rw [String.empty_append, nameStart_thm ht]
  · rw [digitsToString, digitsToNat, String.append_assoc]
    suffices unmangleAux.decodeNum (s.push (adigit c) ++ (digitsToString l ++ ("_" ++ mangleSuffix false nm)))
        ((s.push (adigit c)).posBetween (digitsToString l ++ ("_" ++ mangleSuffix false nm))) res (acc * 10 + ↑c) =
        res.num (digitsToNat l (acc * 10 + ↑c)) +-+! nm by
      as_aux_lemma => rw [unmangleAux.decodeNum]; simpa
    rw [decodeNum_thm rfl]
termination_by 2 * t.length
decreasing_by
  · rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 _; clear a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    rw [ht] at h
    subst h
    simp +arith [String.length_mk]
  · rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12; clear a1 a2 a4 a5 a6 a7 a8 a9 a10 a11 a12
    subst hl_eq h
    simp [digitsToString]

theorem nameStart_thm (h : mangleSuffix b nm = "_" ++ t) :
    unmangleAux.nameStart (s ++ t) (s.posBetween t) res = res +-+! nm := by
  revert h; fun_cases mangleSuffix
  · simp
  split
  · intro ht
    rw [show "_00" = "_" ++ "00" from rfl, @String.append_assoc "_", @String.append_assoc "_",
      String.append_right_inj, String.append_assoc] at ht
    subst ht
    rename_i n' s' m hm
    suffices Lean.Name.unmangleAux _
        (((s.push '0').push '0').posBetween ("" ++ (m ++ mangleSuffix (tailUnderscore s') n')))
        res "" 0 = res.str s' +-+! n' by
      simpa [unmangleAux.nameStart, -String.String.mk_eq_asString]
    rw [String.posBetween_congr rfl ((by conv => lhs; simp)), unmangleAux_cast]
    rw [unmangleAux_thm s' n' false rfl, String.empty_append]
  · intro ht
    rw [String.append_assoc, String.append_right_inj] at ht
    rename_i h
    simp only [not_or, Bool.not_eq_true] at h
    rw [extendRev, unmangleAux_nameStart_normal_str ht.symm h.2]
    intros
    rw [unmangleAux_thm _ _ false]
    assumption
  · intro ht
    rw [String.append_assoc, String.append_assoc, String.append_right_inj] at ht
    subst ht
    rename_i n i
    generalize hr : i.repr = r
    obtain ⟨l, lds, lstr, lnum⟩ := Nat.exists_repr_eq i
    rw [← lstr] at hr
    rw [← lnum, ← hr]
    obtain ⟨d, ds, rfl⟩ := List.ne_nil_iff_exists_cons.mp lds.1
    rw [digitsToString]
    rw [String.append_assoc, unmangleAux.nameStart]
    rw [dif_neg (by simp), if_pos (by simp)]
    rw [dif_neg]
    · simp only [String.next_posBetween_singleton_append, String.get_posBetween_singleton_append,
        unmangleAux_decodeNum_cast, extendRev]
      simp only [val_adigit, UInt32.add_sub_cancel, UInt32.toNat_ofNatLT]
      rw [decodeNum_thm rfl, digitsToNat, Nat.zero_mul, Nat.zero_add]
    · suffices d = 0 → ¬((s.push (adigit d)).posBetween
          (digitsToString ds ++ ("_" ++ mangleSuffix false n))).get (by simp) = '0' by simpa
      rintro rfl
      simp only [IsDigits, Fin.isValue, ne_eq, reduceCtorEq, not_false_eq_true, List.head?_cons,
        List.cons.injEq, true_and, forall_const] at lds
      subst lds
      conv => arg 1; lhs; arg 1; apply String.posBetween_congr rfl; simp [digitsToString]
      simp
termination_by 2 * t.length
decreasing_by
  · assumption
  · rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 _ _
    clear a1 a2 a3 a4 a5 a6 a7 a8 a9
    rw [show "_00" = "_" ++ "00" by rfl, String.append_assoc, String.append_assoc,
      String.append_right_inj] at ht
    simp +arith [← ht, String.length_mk]
  · rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 _ _ _ _ a15 _ _ a18
    clear a1 a2 a3 a4 a5 a6 a7 a8
    simp only [String.append_assoc, String.append_right_inj, ← a15] at ht
    simp [← ht, a18, digitsToString]

end

def extendDisamb (b : Bool) (n : Name) : Bool :=
  match n with
  | .anonymous => b
  | .str n s => extendDisamb (tailUnderscore s) n
  | .num n _ => extendDisamb false n

@[simp]
theorem mangleSuffix_extend (b : Bool) (n n' : Name) :
    mangleSuffix b (n +-+ n') = mangleSuffix b n' ++ mangleSuffix (extendDisamb b n') n := by
  induction n' generalizing b with
  | anonymous => rfl
  | str pre s ih => simp only [extend, mangleSuffix, ih, String.append_assoc, extendDisamb]
  | num pre n ih => simp only [extend, mangleSuffix, ih, String.append_assoc, extendDisamb]

theorem needDisambiguation_def :
    needDisambiguation prev next ↔ extendDisamb false (anonymous +-+! prev) ∨
      checkDisambiguation next next.startValidPos := by
  cases prev
  · rw [needDisambiguation]
    · simp [extendDisamb]
    · simp
  · rw [needDisambiguation, ← tailUnderscore]
    simp only [Bool.or_eq_true, extendRev]
    apply or_congr_left
    rw [extendRev_eq_extend]
    rename_i pre _
    generalize false = b; generalize anonymous +-+! pre = pre; symm
    induction pre generalizing b <;> simp_all [extendDisamb, -Bool.forall_bool]
  · rw [needDisambiguation]
    · simp only [Bool.false_or, extendRev, iff_or_self]
      intro h; exfalso; revert h; rw [imp_false]
      rw [extendRev_eq_extend]
      rename_i pre _
      generalize false = b; generalize anonymous +-+! pre = pre
      induction pre generalizing b <;> simp_all [extendDisamb, -Bool.forall_bool]
    · simp

theorem mangleSuffix_eq_mangleAux (n : Name) (hn : n ≠ anonymous) :
    mangleSuffix false (anonymous +-+! n) = "_" ++ n.mangleAux := by
  induction n with
  | anonymous => contradiction
  | str pre s ih =>
    by_cases hpre : pre = anonymous
    · rw [hpre, mangleAux]
      simp only [extendRev, mangleSuffix, Bool.false_eq_true, false_or, String.append_empty]
      split
      · rw [← String.append_assoc]; rfl
      · rfl
    · simp only [extendRev, mangleAux]
      rw [extendRev_eq_extend, mangleSuffix_extend]
      simp [mangleSuffix, needDisambiguation_def, ih hpre, String.append_assoc]
  | num pre i ih =>
    by_cases hpre : pre = anonymous
    · simp [hpre, mangleAux, mangleSuffix, String.append_assoc]
    · simp only [extendRev]
      rw [extendRev_eq_extend]
      simp [ih hpre, mangleAux, mangleSuffix, String.append_assoc]

theorem unmangle_mangleAux (n : Name) : unmangle n.mangleAux = n := by
  by_cases hn : n = anonymous
  · rw [hn]
    simp [unmangle, unmangleAux.nameStart]
  · rw [unmangle, String.startValidPos_eq_posBetween', unmangleAux_nameStart_cast,
      nameStart_thm (mangleSuffix_eq_mangleAux n hn)]
    simp [extendRev_extendRev]

theorem mangle_inj {n n' : Name} : n.mangle = n'.mangle ↔ n = n' := by
  simp only [mangle, String.append_right_inj]
  constructor
  · intro h
    simpa [unmangle_mangleAux] using congrArg unmangle h
  · exact congrArg mangleAux
