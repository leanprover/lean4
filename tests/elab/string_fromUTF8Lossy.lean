module

import Init.Data.String.Basic

/-!
Tests `String.fromUTF8Lossy` and its model `ByteArray.utf8DecodeLossy`. Valid input round-trips,
and whenever decoding fails at a byte, that byte together with the continuation bytes that follow
it becomes a single `�` (`U+FFFD`). The surrogate cases matter for consumers that rely on one
replacement character per surrogate code point.
-/

/--
`#lossy [bytes] => s` checks that the bytes decode to `s`, by compiled evaluation of the
implementation and of the model, and by `decide_cbv`.
-/
macro "#lossy " "[" bs:term,* "]" " => " s:term : command =>
  `(#guard String.fromUTF8Lossy ⟨#[$bs,*]⟩ == $s
    #guard (⟨#[$bs,*]⟩ : ByteArray).utf8DecodeLossy.toList == ($s : String).toList
    example : String.fromUTF8Lossy ⟨#[$bs,*]⟩ = $s := by decide_cbv)

-- Valid input
#lossy [] => ""
#lossy [0x61, 0x62, 0x63] => "abc"
#lossy [0xC3, 0xA9] => "é"
#lossy [0xE2, 0x82, 0xAC] => "€"
#lossy [0xF0, 0x9F, 0x98, 0x80] => "😀"

-- Invalid lead bytes
#lossy [0x61, 0xFF, 0x62] => "a\ufffdb"
-- The slow path reduces in the kernel as well
example : String.fromUTF8Lossy ⟨#[0x61, 0xFF, 0x62]⟩ = "a\ufffdb" := by decide
#lossy [0xFF, 0xFF] => "\ufffd\ufffd"
#lossy [0xF8, 0x88, 0x80, 0x80, 0x80] => "\ufffd"

-- Truncated sequences
#lossy [0xC3] => "\ufffd"
#lossy [0xC3, 0xFF] => "\ufffd\ufffd"
#lossy [0xE2, 0x82] => "\ufffd"
#lossy [0xE2, 0x82, 0x41] => "\ufffdA"
#lossy [0xF0, 0x9F, 0x98] => "\ufffd"
#lossy [0x41, 0xC3, 0xA9, 0xF0, 0x9F, 0x98] => "Aé\ufffd"

-- Stray continuation bytes
#lossy [0x80, 0x80, 0x41] => "\ufffdA"
#lossy [0xE2, 0x82, 0xAC, 0x80] => "€\ufffd"
#lossy [0xC2, 0x80, 0x80, 0x80] => "\u0080\ufffd"

-- Overlong encodings and out-of-range values
#lossy [0xC0, 0x80] => "\ufffd"
#lossy [0xE0, 0x80, 0x80] => "\ufffd"
#lossy [0xF4, 0x90, 0x80, 0x80] => "\ufffd"
#lossy [0xC0, 0xAF, 0xE0, 0x80, 0xBF, 0xF0, 0x81, 0x82, 0x41] => "\ufffd\ufffd\ufffdA"

-- Round trips through the fast path
#guard String.fromUTF8Lossy "$£€𐍈".toUTF8 == "$£€𐍈"
#guard
  let s := "Zażółć gęślą jaźń 日本語テキスト 😀"
  String.fromUTF8Lossy s.toUTF8 == s

-- A valid prefix is decoded unchanged, whatever follows it
#guard
  let s := "Zażółć 😀"
  let b : ByteArray := ⟨#[0xED, 0xA0, 0x80, 0x41, 0xFF]⟩
  String.fromUTF8Lossy (s.toUTF8 ++ b) == s ++ String.fromUTF8Lossy b

-- Encoded surrogates: one `�` per surrogate code point
#lossy [0xED, 0xA0, 0x80] => "\ufffd"
#lossy [0xED, 0xBF, 0xBF] => "\ufffd"
#lossy [0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80] => "\ufffd\ufffd"
#lossy [0xED, 0xA0, 0x80, 0x41] => "\ufffdA"
#lossy [0x41, 0xED, 0xB0, 0x80] => "A\ufffd"
#lossy [0xE2, 0x82, 0xAC, 0xED, 0xA0, 0x80, 0xF0, 0x9F, 0x98, 0x80] => "€\ufffd😀"
#guard (String.fromUTF8Lossy ⟨#[0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]⟩).length == 2
#guard
  (String.fromUTF8Lossy ⟨#[0xE2, 0x82, 0xAC, 0xED, 0xA0, 0x80, 0xF0, 0x9F, 0x98, 0x80]⟩).length == 3

namespace Test

theorem ByteArray.utf8DecodeChar?_surrogate_append {x y : UInt8} {b : ByteArray}
    (hx : 0xa0 ≤ x ∧ x ≤ 0xbf) (hy : 0x80 ≤ y ∧ y ≤ 0xbf) :
    ByteArray.utf8DecodeChar? ([0xed, x, y].toByteArray ++ b) 0 = none := by
  have h₃ : ByteArray.utf8DecodeChar?.assemble₃ 0xed x y = none := by
    have key : ∀ i, i < 32 → ∀ j, j < 64 → ∀ hm hn,
        ByteArray.utf8DecodeChar?.assemble₃ 0xed ⟨⟨⟨0xa0 + i, hm⟩⟩⟩ ⟨⟨⟨0x80 + j, hn⟩⟩⟩ = none := by
      decide +kernel
    obtain ⟨⟨⟨m, hm⟩⟩⟩ := x
    obtain ⟨⟨⟨n, hn⟩⟩⟩ := y
    obtain ⟨hx₁, hx₂⟩ : 0xa0 ≤ m ∧ m ≤ 0xbf := hx
    obtain ⟨hy₁, hy₂⟩ : 0x80 ≤ n ∧ n ≤ 0xbf := hy
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hx₁
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hy₁
    exact key i (by omega) j (by omega) hm hn
  have hsize : 3 ≤ ([0xed, x, y].toByteArray ++ b).size := by simp
  have h₀ : ([0xed, x, y].toByteArray ++ b)[0]'(by omega) = 0xed := by simp
  have hp₀ : ByteArray.utf8DecodeChar?.parseFirstByte 0xed = .twoMore := rfl
  rw [ByteArray.utf8DecodeChar?, dite_eq_left (by omega), h₀]
  split <;> rename_i hp <;> simp only [hp₀, reduceCtorEq] at hp
  rw [dite_eq_left (by omega)]
  simpa using h₃

theorem ByteArray.utf8DecodeLossy_surrogate_append {x y : UInt8} {b : ByteArray}
    (hx : 0xa0 ≤ x ∧ x ≤ 0xbf) (hy : 0x80 ≤ y ∧ y ≤ 0xbf)
    (hb : ∀ (h : 0 < b.size), ¬ b[0].IsUTF8ContinuationByte) :
    ([0xed, x, y].toByteArray ++ b).utf8DecodeLossy = #['\ufffd'] ++ b.utf8DecodeLossy := by
  apply ByteArray.utf8DecodeLossy_append_of_utf8DecodeChar?_eq_none (by simp)
    (ByteArray.utf8DecodeChar?_surrogate_append hx hy) _ hb
  intro i hi h₀
  have hi' : i < 3 := by simpa using hi
  rw [List.getElem_toByteArray]
  obtain (rfl|rfl) : i = 1 ∨ i = 2 := by omega
  · exact UInt8.isUTF8ContinuationByte_iff.2 ⟨UInt8.le_trans (by decide) hx.1, hx.2⟩
  · exact UInt8.isUTF8ContinuationByte_iff.2 hy

theorem String.fromUTF8Lossy_surrogate_append {x y : UInt8} {b : ByteArray}
    (hx : 0xa0 ≤ x ∧ x ≤ 0xbf) (hy : 0x80 ≤ y ∧ y ≤ 0xbf)
    (hb : ∀ (h : 0 < b.size), ¬ b[0].IsUTF8ContinuationByte) :
    String.fromUTF8Lossy ([0xed, x, y].toByteArray ++ b) =
      String.singleton '\ufffd' ++ String.fromUTF8Lossy b := by
  rw [String.fromUTF8Lossy_eq_ofList, String.fromUTF8Lossy_eq_ofList,
    ByteArray.utf8DecodeLossy_surrogate_append hx hy hb, Array.toList_append, List.toList_toArray,
    String.ofList_append, String.singleton_eq_ofList]

end Test
