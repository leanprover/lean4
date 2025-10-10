module
import all Lean.Compiler.NameMangling
import all Init.Data.String.Basic
import all Init.Data.Repr

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
theorem String.append_right_inj {t₁ t₂ : String} (s : String) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ := by
  simp [ByteArray.append_right_inj, ← String.bytes_inj]

def String.posBetween (s t : String) : (s ++ t).ValidPos :=
  ⟨s.endPos, by simp [Pos.Raw.isValid_append]⟩

@[simp]
theorem String.posBetween_eq_endValidPos_iff (s t : String) :
    s.posBetween t = (s ++ t).endValidPos ↔ t = "" := by
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

def encodeHex (n val : Nat) : String :=
  match n with
  | 0 => ""
  | k + 1 => (String.singleton <| Nat.digitChar (val / 16 ^ k)) ++ encodeHex k (val % 16 ^ k)

@[simp]
theorem String.push_ne_empty : String.push s c ≠ "" := by
  simp [← String.bytes_inj]

@[simp]
theorem String.singleton_ne_empty : String.singleton c ≠ "" := by
  simp [← String.bytes_inj]

@[simp]
theorem checkLowerHex_uncast {s t : String} {p : t.ValidPos} (h : t = s) :
    Lean.checkLowerHex n s (p.cast h) = Lean.checkLowerHex n t p := by
  cases h; rfl

@[simp]
theorem parseLowerHex_uncast {s t : String} {p : t.ValidPos} (h : t = s) (h') :
    Lean.parseLowerHex n s (p.cast h) h' i = Lean.parseLowerHex n t p (by cases h; exact h') i := by
  cases h; rfl

theorem checkLowerHex_encodeHex (h : val < 16 ^ n) :
    Lean.checkLowerHex n (s ++ encodeHex n val) (String.posBetween _ _) = true := by
  fun_induction encodeHex generalizing s
  · rfl
  · rename_i val k ih
    have h' : val % 16 ^ k < 16 ^ k := Nat.mod_lt _ (Nat.pow_pos (by decide))
    suffices (val / 16 ^ k).digitChar.isDigit = true ∨
        97 ≤ (val / 16 ^ k).digitChar.val ∧ (val / 16 ^ k).digitChar.val ≤ 102 by
      simpa [Lean.checkLowerHex, ih h']
    rw [Nat.pow_succ] at h
    have h'' : val / 16 ^ k < 16 := by
      rwa [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm]
    generalize val / 16 ^ k = c at h''
    decide +revert

theorem Nat.digitChar_eq (n : Nat) (h : n < 16) : n.digitChar =
    if h : n < 10 then
      ⟨UInt32.ofNatLT (48 + n) (by grind), by grind [UInt32.toNat_ofNatLT]⟩
    else
      ⟨UInt32.ofNatLT (87 + n) (by grind), by grind [UInt32.toNat_ofNatLT]⟩ := by
  decide +revert

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

theorem parseLowerHex_encodeHex (h : val < 16 ^ n) (h') :
    Lean.parseLowerHex n (s ++ encodeHex n val) (String.posBetween _ _) h' i =
        i * 16 ^ n + val := by
  fun_induction encodeHex generalizing s i
  · simp_all [Lean.parseLowerHex]
  · rename_i val k ih
    have h' : val % 16 ^ k < 16 ^ k := Nat.mod_lt _ (Nat.pow_pos (by decide))
    simp [Lean.parseLowerHex, ih h']
    rw [Nat.pow_succ] at h
    have h'' : val / 16 ^ k < 16 := by
      rwa [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm]
    rw [Nat.mod_eq_sub]
    generalize hc : val / 16 ^ k = c at h''
    rw [Char.isDigit]
    simp only [ge_iff_le, Bool.and_eq_true, decide_eq_true_eq]
    have this (a h) := Nat.shiftLeft_or_eq_add i 4 a h
    simp only [Nat.reducePow] at this
    rw [Nat.pow_succ, Nat.mul_comm _ 16, ← Nat.mul_assoc, ← apply_ite (· + _)]
    have : i * 16 * 16 ^ k + val = (i * 16 + c) * 16 ^ k + (val - 16 ^ k * c) := by
      rw [Nat.add_mul, Nat.mul_comm c, Nat.add_assoc, Nat.add_sub_cancel']
      rw [← hc, Nat.mul_comm]
      exact Nat.div_mul_le_self val (16 ^ k)
    rw [this, Nat.add_right_cancel_iff]; clear this
    rw [← this c h'']; clear this hc
    split <;> (congr; decide +revert)

def Char.mangle (c : Char) : String :=
  if c.isDigit ∨ c.isAlpha then String.singleton c
  else if c = '_' then "__"
  else if c.val < 0x100 then "_x" ++ encodeHex 2 c.toNat
  else if c.val < 0x10000 then "_u" ++ encodeHex 4 c.toNat
  else "_U" ++ encodeHex 8 c.toNat

theorem String.something_uhh (n : Nat) (h : n < 16 ^ k) :
    List.foldl (fun r c => r.push c)
      (Nat.repeat (fun x => x.push '0') (k - (Nat.toDigits 16 n).length) (s ++ "_U"))
      (Nat.toDigits 16 n) = encodeHex k n := by
  sorry

#check (rfl : Lean.Name.mangle `abc.c == "abc_c")

theorem String.mangleAux_normalize : mangleAux n it s = s ++ mangleAux n it "" := by
  induction n generalizing it s with
  | zero => simp [String.mangleAux]
  | succ k ih =>
    unfold String.mangleAux
    extract_lets
    split
    · conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp only [String.push_eq_append, String.empty_append, String.append_assoc]
    split
    · conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp only [String.empty_append, String.append_assoc]
    split
    · conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp +zetaDelta only [String.push_eq_append, String.empty_append, String.append_assoc]
    split
    · conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp +zetaDelta only [String.push_eq_append, String.empty_append, String.append_assoc]
    · conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp +zetaDelta only [String.push_eq_append, String.empty_append, String.append_assoc]

theorem String.mangle_eq_empty : mangle s = "" ↔ s = "" := by
  rw [String.mangle]
  generalize hlen : s.length = len
  generalize hit : s.mkIterator = it
  generalize hacc : "" = acc
  fun_cases String.mangleAux <;> subst hacc hit
  · simp_all
  ·

#print String.mangleAux.fun_cases_unfolding

namespace Lean.Name

theorem mangleAux_eq_empty : mangleAux nm = "" ↔ nm = .anonymous := by
  constructor
  rotate_left
  · rintro rfl; rfl
  fun_cases mangleAux
  · simp
  · simp
  · rename_i s m h

mutual

theorem nameStart_thm (hn : (mangleAux nm).length ≤ n) :
    unmangleAux.nameStart (s ++ mangleAux nm) (s.endValidPos.appendRight _) res n = res ++ nm := by
  fun_cases unmangleAux.nameStart
  · simp at hn

end

theorem unmangle_mangleAux (n : Name) : unmangle n.mangleAux = n := by
  sorry

theorem mangle_inj {n n' : Name} : n.mangle = n'.mangle ↔ n = n' := by
  simp only [mangle, String.append_right_inj]
  constructor
  · intro h
    simpa [unmangle_mangleAux] using congrArg unmangle h
  · exact congrArg mangleAux
