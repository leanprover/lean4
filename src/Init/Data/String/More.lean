/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Extern

universe u

def List.asString (s : List Char) : String :=
  ⟨s⟩

namespace String

@[reducible] protected def le (a b : String) : Prop := ¬ b < a

instance : LE String :=
  ⟨String.le⟩

instance decLE (s₁ s₂ : String) : Decidable (s₁ ≤ s₂) :=
  inferInstanceAs (Decidable (Not _))

/--
Converts a string to a list of characters.

Even though the logical model of strings is as a structure that wraps a list of characters,
this operation takes time and space linear in the length of the string, because the compiler
uses an optimized representation as dynamic arrays.

Example: `"abc".toList = ['a', 'b', 'c']`
-/
def toList (s : String) : List Char :=
  s.data

/--
Replaces the character at position `p` in the string `s` with the result of applying `f` to that character.
If `p` is an invalid position, the string is returned unchanged.

Examples:
* `abc.modify ⟨1⟩ Char.toUpper = "aBc"`
* `abc.modify ⟨3⟩ Char.toUpper = "abc"`
-/
def modify (s : String) (i : Pos) (f : Char → Char) : String :=
  s.set i <| f <| s.get i

theorem one_le_csize (c : Char) : 1 ≤ csize c := by
  repeat first | apply iteInduction (motive := (1 ≤ UInt32.toNat ·)) <;> intros | decide

@[simp] theorem pos_lt_eq (p₁ p₂ : Pos) : (p₁ < p₂) = (p₁.1 < p₂.1) := rfl

@[simp] theorem pos_add_char (p : Pos) (c : Char) : (p + c).byteIdx = p.byteIdx + csize c := rfl

theorem lt_next (s : String) (i : Pos) : i.1 < (s.next i).1 :=
  Nat.add_lt_add_left (one_le_csize _) _

theorem utf8PrevAux_lt_of_pos : ∀ (cs : List Char) (i p : Pos), p ≠ 0 →
    (utf8PrevAux cs i p).1 < p.1
  | [], i, p, h =>
    Nat.lt_of_le_of_lt (Nat.zero_le _)
      (Nat.zero_lt_of_ne_zero (mt (congrArg Pos.mk) h))
  | c::cs, i, p, h => by
    simp [utf8PrevAux]
    apply iteInduction (motive := (Pos.byteIdx · < _)) <;> intro h'
    next => exact h' ▸ Nat.add_lt_add_left (one_le_csize _) _
    next => exact utf8PrevAux_lt_of_pos _ _ _ h

theorem prev_lt_of_pos (s : String) (i : Pos) (h : i ≠ 0) : (s.prev i).1 < i.1 := by
  simp [prev, h]
  exact utf8PrevAux_lt_of_pos _ _ _ h

def posOfAux (s : String) (c : Char) (stopPos : Pos) (pos : Pos) : Pos :=
  if h : pos < stopPos then
    if s.get pos == c then pos
    else
      have := Nat.sub_lt_sub_left h (lt_next s pos)
      posOfAux s c stopPos (s.next pos)
  else pos
termination_by stopPos.1 - pos.1

/--
Returns the position of the first occurrence of a character, `c`, in `s`.
If `s` does not contain `c`, returns `s.endPos`.

Examples:
* `"abba".posOf 'a' = ⟨0⟩`
* `"abba".posOf 'z' = ⟨4⟩`
* `"L∃∀N".posOf '∀' = ⟨4⟩`
-/
@[inline] def posOf (s : String) (c : Char) : Pos :=
  posOfAux s c s.endPos 0

def revPosOfAux (s : String) (c : Char) (pos : Pos) : Option Pos :=
  if h : pos = 0 then none
  else
    have := prev_lt_of_pos s pos h
    let pos := s.prev pos
    if s.get pos == c then some pos
    else revPosOfAux s c pos
termination_by pos.1

/--
Returns the position of the last occurrence of a character, `c`, in `s`.
If `s` does not contain `c`, returns `none`.

Examples:
* `"abba".posOf 'a' = some ⟨3⟩`
* `"abba".posOf 'z' = none`
* `"L∃∀N".posOf '∀' = some ⟨4⟩`
-/
def revPosOf (s : String) (c : Char) : Option Pos :=
  revPosOfAux s c s.endPos

abbrev Pos.min (p₁ p₂ : Pos) : Pos :=
  { byteIdx := p₁.byteIdx.min p₂.byteIdx }

/-- Returns the first position where the two strings differ. -/
def firstDiffPos (a b : String) : Pos :=
  let stopPos := a.endPos.min b.endPos
  let rec loop (i : Pos) : Pos :=
    if h : i < stopPos then
      if a.get i != b.get i then i
      else
        have := Nat.sub_lt_sub_left h (lt_next a i)
        loop (a.next i)
    else i
    termination_by stopPos.1 - i.1
  loop 0

/--
Auxiliary for `splitOn`. Preconditions:
* `sep` is not empty
* `b <= i` are indexes into `s`
* `j` is an index into `sep`, and not at the end

It represents the state where we have currently parsed some split parts into `r` (in reverse order),
`b` is the beginning of the string / the end of the previous match of `sep`, and the first `j` bytes
of `sep` match the bytes `i-j .. i` of `s`.
-/
def splitOnAux (s sep : String) (b : Pos) (i : Pos) (j : Pos) (r : List String) : List String :=
  if s.atEnd i then
    let r := (s.extract b i)::r
    r.reverse
  else
    if s.get i == sep.get j then
      let i := s.next i
      let j := sep.next j
      if sep.atEnd j then
        splitOnAux s sep i i 0 (s.extract b (i - j)::r)
      else
        splitOnAux s sep b i j r
    else
      splitOnAux s sep b (s.next (i - j)) 0 r
termination_by (s.endPos.1 - (i - j).1, sep.endPos.1 - j.1)
decreasing_by
  all_goals simp_wf
  focus
    rename_i h _ _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (lt_next s _))
  focus
    rename_i i₀ j₀ _ eq h'
    rw [show (s.next i₀ - sep.next j₀).1 = (i₀ - j₀).1 by
      show (_ + csize _) - (_ + csize _) = _
      rw [(beq_iff_eq ..).1 eq, Nat.add_sub_add_right]; rfl]
    right; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.le_add_right ..) (Nat.gt_of_not_le (mt decide_eq_true h')))
      (lt_next sep _)
  focus
    rename_i h _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (lt_next s _)

/--
Splits a string `s` on occurrences of the separator `sep`. When `sep` is empty, it returns `[s]`;
when `sep` occurs in overlapping patterns, the first match is taken. There will always be exactly
`n+1` elements in the returned list if there were `n` nonoverlapping matches of `sep` in the string.
The default separator is `" "`. The separators are not included in the returned substrings.

```
"here is some text ".splitOn = ["here", "is", "some", "text", ""]
"here is some text ".splitOn "some" = ["here is ", " text "]
"here is some text ".splitOn "" = ["here is some text "]
"ababacabac".splitOn "aba" = ["", "bac", "c"]
```
-/
def splitOn (s : String) (sep : String := " ") : List String :=
  if sep == "" then [s] else splitOnAux s sep 0 0 0 []

instance : Inhabited String := ⟨""⟩

instance : Append String := ⟨String.append⟩

@[deprecated push (since := "2024-04-06")]
def str : String → Char → String := push

def pushn (s : String) (c : Char) (n : Nat) : String :=
  n.repeat (fun s => s.push c) s

def isEmpty (s : String) : Bool :=
  s.endPos == 0

def join (l : List String) : String :=
  l.foldl (fun r s => r ++ s) ""

def singleton (c : Char) : String :=
  "".push c

def intercalate (s : String) : List String → String
  | []      => ""
  | a :: as => go a s as
where go (acc : String) (s : String) : List String → String
  | a :: as => go (acc ++ s ++ a) s as
  | []      => acc

def offsetOfPosAux (s : String) (pos : Pos) (i : Pos) (offset : Nat) : Nat :=
  if i >= pos then offset
  else if h : s.atEnd i then
    offset
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next s _)
    offsetOfPosAux s pos (s.next i) (offset+1)
termination_by s.endPos.1 - i.1

def offsetOfPos (s : String) (pos : Pos) : Nat :=
  offsetOfPosAux s pos 0 0

theorem utf8SetAux_of_gt (c' : Char) : ∀ (cs : List Char) {i p : Pos}, i > p → utf8SetAux c' cs i p = cs
  | [],    _, _, _ => rfl
  | c::cs, i, p, h => by
    rw [utf8SetAux, if_neg (mt (congrArg (·.1)) (Ne.symm <| Nat.ne_of_lt h)), utf8SetAux_of_gt c' cs]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

theorem set_next_add (s : String) (i : Pos) (c : Char) (b₁ b₂)
    (h : (s.next i).1 + b₁ = s.endPos.1 + b₂) :
    ((s.set i c).next i).1 + b₁ = (s.set i c).endPos.1 + b₂ := by
  simp [next, get, set, endPos, utf8ByteSize] at h ⊢
  rw [Nat.add_comm i.1, Nat.add_assoc] at h ⊢
  let rec foo : ∀ cs a b₁ b₂,
    csize (utf8GetAux cs a i) + b₁ = utf8ByteSize.go cs + b₂ →
    csize (utf8GetAux (utf8SetAux c cs a i) a i) + b₁ = utf8ByteSize.go (utf8SetAux c cs a i) + b₂
  | [], _, _, _, h => h
  | c'::cs, a, b₁, b₂, h => by
    unfold utf8SetAux
    apply iteInduction (motive := fun p => csize (utf8GetAux p a i) + b₁ = utf8ByteSize.go p + b₂) <;>
      intro h' <;> simp [utf8GetAux, h', utf8ByteSize.go] at h ⊢
    next =>
      rw [Nat.add_assoc, Nat.add_left_comm] at h ⊢; rw [Nat.add_left_cancel h]
    next =>
      rw [Nat.add_assoc] at h ⊢
      refine foo cs (a + c') b₁ (csize c' + b₂) h
  exact foo s.1 0 _ _ h

theorem mapAux_lemma (s : String) (i : Pos) (c : Char) (h : ¬s.atEnd i) :
    (s.set i c).endPos.1 - ((s.set i c).next i).1 < s.endPos.1 - i.1 :=
  suffices (s.set i c).endPos.1 - ((s.set i c).next i).1 = s.endPos.1 - (s.next i).1 by
    rw [this]
    apply Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next ..)
  Nat.sub.elim (motive := (_ = ·)) _ _
    (fun _ k e =>
      have := set_next_add _ _ _ k 0 e.symm
      Nat.sub_eq_of_eq_add <| this.symm.trans <| Nat.add_comm ..)
    (fun h => by
      have ⟨k, e⟩ := Nat.le.dest h
      rw [Nat.succ_add] at e
      have : ((s.set i c).next i).1 = _ := set_next_add _ _ c 0 k.succ e.symm
      exact Nat.sub_eq_zero_of_le (this ▸ Nat.le_add_right ..))

@[specialize] def mapAux (f : Char → Char) (i : Pos) (s : String) : String :=
  if h : s.atEnd i then s
  else
    let c := f (s.get i)
    have := mapAux_lemma s i c h
    let s := s.set i c
    mapAux f (s.next i) s
termination_by s.endPos.1 - i.1

@[inline] def map (f : Char → Char) (s : String) : String :=
  mapAux f 0 s

/--
Return `true` iff the substring of byte size `sz` starting at position `off1` in `s1` is equal to that starting at `off2` in `s2.`.
False if either substring of that byte size does not exist. -/
def substrEq (s1 : String) (off1 : String.Pos) (s2 : String) (off2 : String.Pos) (sz : Nat) : Bool :=
  off1.byteIdx + sz ≤ s1.endPos.byteIdx && off2.byteIdx + sz ≤ s2.endPos.byteIdx && loop off1 off2 { byteIdx := off1.byteIdx + sz }
where
  loop (off1 off2 stop1 : Pos) :=
    if _h : off1.byteIdx < stop1.byteIdx then
      let c₁ := s1.get off1
      let c₂ := s2.get off2
      c₁ == c₂ && loop (off1 + c₁) (off2 + c₂) stop1
    else true
  termination_by stop1.1 - off1.1
  decreasing_by
    have := Nat.sub_lt_sub_left _h (Nat.add_lt_add_left (one_le_csize c₁) off1.1)
    decreasing_tactic

/-- Return true iff `p` is a prefix of `s` -/
def isPrefixOf (p : String) (s : String) : Bool :=
  substrEq p 0 s 0 p.endPos.byteIdx

/-- Replace all occurrences of `pattern` in `s` with `replacement`. -/
def replace (s pattern replacement : String) : String :=
  if h : pattern.endPos.1 = 0 then s
  else
    have hPatt := Nat.zero_lt_of_ne_zero h
    let rec loop (acc : String) (accStop pos : String.Pos) :=
      if h : pos.byteIdx + pattern.endPos.byteIdx > s.endPos.byteIdx then
        acc ++ s.extract accStop s.endPos
      else
        have := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hPatt _) (Nat.ge_of_not_lt h)
        if s.substrEq pos pattern 0 pattern.endPos.byteIdx then
          have := Nat.sub_lt_sub_left this (Nat.add_lt_add_left hPatt _)
          loop (acc ++ s.extract accStop pos ++ replacement) (pos + pattern) (pos + pattern)
        else
          have := Nat.sub_lt_sub_left this (lt_next s pos)
          loop acc accStop (s.next pos)
      termination_by s.endPos.1 - pos.1
    loop "" 0 0

end String
