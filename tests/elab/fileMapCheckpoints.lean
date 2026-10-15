module
import all Lean.Data.Position

/-!
Proves that the per-line column checkpoints of `FileMap` (#15646) do not change the results of
`FileMap.toPosition` and `FileMap.codepointPosToUtf16Pos`: for every string, both functions return
the same on `FileMap.ofString s` as on the same map without checkpoints.

`ofString` records each checkpoint after walking `column` characters with `String.Pos.Raw.next`
from the start of its line (`Valid`), and both lookups only ever resume such a walk from a
checkpoint they found on the same line. This part therefore never reasons about UTF-8 itself.

Building on that, the second half specifies `ofString`, `lineStart`, `toPosition` and
`codepointPosToUtf16Pos` against `s.toList`, with `off s k` the byte offset of the first `k`
characters (`toPosition_ofString_spec`, `lineStart_ofString`,
`codepointPosToUtf16Pos_ofString_spec`).
-/

open Lean

namespace FileMapCheckpoints

/-! ## Walking and UTF-16 sums -/

open Lean.String (codepointPosToUtf16PosFromAux codepointPosToUtf16PosFrom)

/-- `n` steps of `(·.next s)` from `i`. -/
def walk (s : String) : String.Pos.Raw → Nat → String.Pos.Raw
  | i, 0 => i
  | i, n+1 => walk s (i.next s) n

theorem walk_add (s : String) (i : String.Pos.Raw) (a b : Nat) :
    walk s i (a + b) = walk s (walk s i a) b := by
  induction a generalizing i <;> grind [walk]

theorem walk_succ (s : String) (i : String.Pos.Raw) (n : Nat) :
    walk s i (n + 1) = (walk s i n).next s := by
  grind [walk_add, walk]

theorem walk_lt (s : String) (i : String.Pos.Raw) {j k : Nat} (h : j < k) :
    (walk s i j).byteIdx < (walk s i k).byteIdx := by
  induction k <;> grind [walk_succ, String.Pos.Raw.byteIdx_lt_byteIdx_next]

theorem aux_shift (s : String) (n : Nat) (i : String.Pos.Raw) (acc : Nat) :
    codepointPosToUtf16PosFromAux s n i acc = acc + codepointPosToUtf16PosFromAux s n i 0 := by
  induction n generalizing i acc <;> grind [codepointPosToUtf16PosFromAux]

theorem aux_add (s : String) (a b : Nat) (i : String.Pos.Raw) (acc : Nat) :
    codepointPosToUtf16PosFromAux s (a + b) i acc =
      codepointPosToUtf16PosFromAux s b (walk s i a) (codepointPosToUtf16PosFromAux s a i acc) := by
  induction a generalizing i acc <;> grind [codepointPosToUtf16PosFromAux, walk]

/-! ## `toColumn` can resume from any intermediate position -/

theorem toColumn_walk (pos : String.Pos.Raw) (s : String) (k : Nat) :
    ∀ (i : String.Pos.Raw) (c : Nat), (∀ j < k, walk s i j ≠ pos ∧ ¬ (walk s i j).atEnd s) →
      FileMap.toPosition.toColumn pos s i c =
        FileMap.toPosition.toColumn pos s (walk s i k) (c + k) := by
  induction k with
  | zero => grind [walk]
  | succ k ih =>
    intro i c h
    have := h 0 (by omega)
    rw [FileMap.toPosition.toColumn]
    grind [walk]

/-! ## Checkpoint search soundness -/

theorem findCheckpoint_loop_sound (fm : FileMap) (line : Nat) (key : ColumnCheckpoint → Nat)
    (x : Nat) (cps : Array ColumnCheckpoint) (lo hi : Nat) (hlo : lo = 0 ∨ key cps[lo-1]! ≤ x)
    (hb : lo ≤ hi ∧ hi ≤ cps.size) :
    FileMap.findCheckpoint.loop fm line key x cps lo hi =
        { pos := fm.lineStart (line + 1), column := 0, utf16Column := 0 } ∨
      ∃ k, ∃ h : k < cps.size, FileMap.findCheckpoint.loop fm line key x cps lo hi = cps[k] ∧
        key cps[k] ≤ x := by
  fun_induction FileMap.findCheckpoint.loop fm line key x cps lo hi <;> grind

theorem findCheckpoint_sound (fm : FileMap) (line : Nat) (key : ColumnCheckpoint → Nat) (x : Nat) :
    fm.findCheckpoint line key x =
        { pos := fm.lineStart (line + 1), column := 0, utf16Column := 0 } ∨
      ∃ h : line < fm.columnCheckpoints.size, ∃ k, ∃ h' : k < fm.columnCheckpoints[line].get.size,
        fm.findCheckpoint line key x = fm.columnCheckpoints[line].get[k] ∧
        key fm.columnCheckpoints[line].get[k] ≤ x := by
  have := findCheckpoint_loop_sound fm line key x
    ((fm.columnCheckpoints[line]?.map (·.get)).getD #[]) 0
    ((fm.columnCheckpoints[line]?.map (·.get)).getD #[]).size (by simp) (by simp)
  by_cases hl : line < fm.columnCheckpoints.size <;> grind [FileMap.findCheckpoint]

/-! ## Validity of the checkpoints computed by `ofString` -/

/-- `cp` is the checkpoint reached by walking from the line start `ls`. -/
def Valid (s : String) (ls : String.Pos.Raw) (cp : ColumnCheckpoint) : Prop :=
  cp.pos = walk s ls cp.column ∧
  cp.utf16Column = codepointPosToUtf16PosFromAux s cp.column ls 0 ∧
  cp.pos.byteIdx < s.utf8ByteSize

def _root_.Lean.FileMap.WF (fm : FileMap) : Prop :=
  fm.columnCheckpoints.size < fm.positions.size ∧
  ∀ b (hb : b < fm.columnCheckpoints.size), ∀ cp ∈ fm.columnCheckpoints[b].get,
    Valid fm.source fm.positions[b]! cp

theorem lineCheckpoints_loop_valid (s : String) (ls le : String.Pos.Raw) (k : Nat)
    (hle : le = walk s ls k) (hk : ∀ j < k, ¬ (walk s ls j).atEnd s)
    (i last : String.Pos.Raw) (column u : Nat) (cps : Array ColumnCheckpoint)
    (hi : i = walk s ls column) (hu : u = codepointPosToUtf16PosFromAux s column ls 0)
    (hc : column ≤ k) (hcps : ∀ cp ∈ cps, Valid s ls cp) :
    ∀ cp ∈ FileMap.lineCheckpoints.loop s le i last column u cps, Valid s ls cp := by
  fun_induction FileMap.lineCheckpoints.loop s le i last column u cps with
  | case1 i last column u cps hlt checkpoint ih =>
    have : column < k := by
      by_cases column = k <;> grind [String.Pos.Raw.lt_iff]
    have := walk_succ s ls column
    have := aux_add s column 1 ls 0
    apply ih <;> grind [Valid, String.Pos.Raw.atEnd, codepointPosToUtf16PosFromAux]
  | case2 => grind

theorem lineCheckpoints_valid (s : String) (ls le : String.Pos.Raw) (k : Nat)
    (hle : le = walk s ls k) (hk : ∀ j < k, ¬ (walk s ls j).atEnd s) :
    ∀ cp ∈ (FileMap.lineCheckpoints s ls le).get, Valid s ls cp := by
  unfold FileMap.lineCheckpoints
  split
  · simp [Thunk.pure, Thunk.get]
  · exact lineCheckpoints_loop_valid s ls le k hle hk _ _ 0 0 _ rfl rfl (by omega) (by simp)

/-- `i` is reached by walking from the start of the current line without reaching the end. -/
def LoopInv (s : String) (i lineStart : String.Pos.Raw) (ps : Array String.Pos.Raw)
    (cps : Array (Thunk (Array ColumnCheckpoint))) : Prop :=
  ps.size = cps.size + 1 ∧
  lineStart = ps[cps.size]! ∧
  (∃ k, i = walk s lineStart k ∧ ∀ j < k, ¬ (walk s lineStart j).atEnd s) ∧
  (∀ b (hb : b < cps.size), ∀ cp ∈ cps[b].get, Valid s ps[b]! cp)

theorem ofString_loop_wf (s : String) (i lineStart : String.Pos.Raw) (ps : Array String.Pos.Raw)
    (cps : Array (Thunk (Array ColumnCheckpoint))) (h : LoopInv s i lineStart ps cps) :
    (FileMap.ofString.loop s i lineStart ps cps).WF := by
  fun_induction FileMap.ofString.loop s i lineStart ps cps with
  | case1 i lineStart ps cps hend =>
    obtain ⟨k, hk, hk'⟩ := h.2.2.1
    have := lineCheckpoints_valid s lineStart i k hk hk'
    grind [FileMap.WF, LoopInv]
  | case2 i lineStart ps cps hend c next hnl ih =>
    obtain ⟨k, hk, hk'⟩ := h.2.2.1
    have := walk_succ s lineStart k
    have := lineCheckpoints_valid s lineStart next (k + 1) (by grind) (by grind)
    refine ih ⟨?_, ?_, ⟨0, rfl, by simp⟩, ?_⟩ <;> grind [LoopInv]
  | case3 i lineStart ps cps hend c next hnl ih =>
    obtain ⟨k, hk, hk'⟩ := h.2.2.1
    have := walk_succ s lineStart k
    grind [LoopInv]

theorem ofString_wf (s : String) : (FileMap.ofString s).WF :=
  ofString_loop_wf s _ _ _ _ ⟨rfl, rfl, ⟨0, rfl, by simp⟩, by simp⟩

/-! ## Main theorems -/

theorem lineStart_succ (fm : FileMap) (b : Nat) (hb : b < fm.positions.size) :
    fm.lineStart (b + 1) = fm.positions[b]! := by
  grind [FileMap.lineStart]

theorem findCheckpoint_empty (fm : FileMap) (line : Nat) (key : ColumnCheckpoint → Nat) (x : Nat) :
    ({ fm with columnCheckpoints := #[] } : FileMap).findCheckpoint line key x =
      { pos := fm.lineStart (line + 1), column := 0, utf16Column := 0 } := by
  grind [FileMap.findCheckpoint, FileMap.findCheckpoint.loop, FileMap.lineStart]

theorem lineStart_pred_succ (fm : FileMap) (line : Nat) :
    fm.lineStart (line - 1 + 1) = fm.lineStart line := by
  cases line <;> grind [FileMap.lineStart]

/-- Without checkpoints, `codepointPosToUtf16Pos` walks from the start of the line. -/
theorem codepointPosToUtf16Pos_empty (fm : FileMap) (line col : Nat) :
    ({ fm with columnCheckpoints := #[] } : FileMap).codepointPosToUtf16Pos line col =
      codepointPosToUtf16PosFrom fm.source col (fm.lineStart line) := by
  simp only [FileMap.codepointPosToUtf16Pos, findCheckpoint_empty, lineStart_pred_succ]
  split <;> simp [FileMap.lineStart]

theorem codepointPosToUtf16Pos_eq (fm : FileMap) (hwf : fm.WF) (line col : Nat) :
    fm.codepointPosToUtf16Pos line col =
      { fm with columnCheckpoints := #[] }.codepointPosToUtf16Pos line col := by
  rw [codepointPosToUtf16Pos_empty]
  simp only [FileMap.codepointPosToUtf16Pos]
  split
  · rfl
  rcases findCheckpoint_sound fm (line - 1) (·.column) col with h | ⟨hb, k, hk, h, hle⟩
  · rw [h, lineStart_pred_succ]; simp
  · have := aux_add fm.source fm.columnCheckpoints[line - 1].get[k].column
      (col - fm.columnCheckpoints[line - 1].get[k].column) fm.positions[line - 1]! 0
    have := hwf.2 (line - 1) hb _ (Array.getElem_mem hk)
    have := lineStart_succ fm (line - 1) (by have := hwf.1; omega)
    have := lineStart_pred_succ fm line
    grind [Valid, FileMap.WF, aux_shift, codepointPosToUtf16PosFrom]

theorem toColumn_findCheckpoint (fm : FileMap) (hwf : fm.WF) (pos : String.Pos.Raw) (b : Nat) :
    let cp := fm.findCheckpoint b (·.pos.byteIdx) pos.byteIdx
    let cp' := ({ fm with columnCheckpoints := #[] } : FileMap).findCheckpoint b (·.pos.byteIdx)
      pos.byteIdx
    FileMap.toPosition.toColumn pos fm.source cp.pos cp.column =
      FileMap.toPosition.toColumn pos fm.source cp'.pos cp'.column := by
  simp only [findCheckpoint_empty]
  rcases findCheckpoint_sound fm b (·.pos.byteIdx) pos.byteIdx with h | ⟨hb, k, hk, h, hle⟩
  · rw [h]
  · have := hwf.2 b hb _ (Array.getElem_mem hk)
    have := toColumn_walk pos fm.source fm.columnCheckpoints[b].get[k].column fm.positions[b]! 0
      fun j hj => by
        have := walk_lt fm.source fm.positions[b]! hj
        grind [Valid, String.Pos.Raw.atEnd]
    grind [Valid, FileMap.WF, lineStart_succ]

theorem toPosition_loop_eq (fm : FileMap) (hwf : fm.WF) (pos : String.Pos.Raw) (b e : Nat) :
    FileMap.toPosition.loop fm pos fm.source fm.positions b e =
      FileMap.toPosition.loop { fm with columnCheckpoints := #[] } pos fm.source fm.positions b
        e := by
  induction h : e - b using Nat.strongRecOn generalizing b e with
  | _ n ih =>
  rw [FileMap.toPosition.loop, FileMap.toPosition.loop]
  have := toColumn_findCheckpoint fm hwf pos b
  have hs : ({ fm with columnCheckpoints := #[] } : FileMap).lineIsShort b = fm.lineIsShort b := rfl
  split
  · simp only [hs]
    split
    · rfl
    · simp only [FileMap.getLine, FileMap.getLastLine] at this ⊢
      rw [this]
  · have := ih (e - (b + e) / 2) (by omega) ((b + e) / 2) e rfl
    have := ih ((b + e) / 2 - b) (by omega) b ((b + e) / 2) rfl
    grind [FileMap.getLine, FileMap.getLastLine]

theorem toPosition_eq (fm : FileMap) (hwf : fm.WF) (pos : String.Pos.Raw) :
    fm.toPosition pos = { fm with columnCheckpoints := #[] }.toPosition pos := by
  have := toPosition_loop_eq fm hwf pos
  simp only [FileMap.toPosition]
  grind [FileMap.getLastLine]

theorem toPosition_ofString (s : String) (pos : String.Pos.Raw) :
    (FileMap.ofString s).toPosition pos =
      { FileMap.ofString s with columnCheckpoints := #[] }.toPosition pos :=
  toPosition_eq _ (ofString_wf s) pos

theorem codepointPosToUtf16Pos_ofString (s : String) (line col : Nat) :
    (FileMap.ofString s).codepointPosToUtf16Pos line col =
      { FileMap.ofString s with columnCheckpoints := #[] }.codepointPosToUtf16Pos line col :=
  codepointPosToUtf16Pos_eq _ (ofString_wf s) line col


/-! ## UTF-8 bridge -/

/-- Sum of the UTF-8 sizes of a list of characters. -/
def bsum : List Char → Nat
  | [] => 0
  | c :: l => c.utf8Size + bsum l

/-- Byte offset of the first `k` characters of `s`. -/
def off (s : String) (k : Nat) : String.Pos.Raw := ⟨bsum (s.toList.take k)⟩

theorem utf8ByteSize_ofList (l : List Char) : (String.ofList l).utf8ByteSize = bsum l := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [String.utf8ByteSize_append, ih, bsum]

theorem utf8ByteSize_eq (s : String) : s.utf8ByteSize = bsum s.toList := by
  rw [← utf8ByteSize_ofList, String.ofList_toList]

theorem bsum_take_succ (l : List Char) (k : Nat) (h : k < l.length) :
    bsum (l.take (k + 1)) = bsum (l.take k) + l[k].utf8Size := by
  induction l generalizing k with
  | nil => simp at h
  | cons c l ih => cases k <;> grind [bsum]

theorem bsum_take_lt (l : List Char) {a b : Nat} (hab : a < b) (hb : b ≤ l.length) :
    bsum (l.take a) < bsum (l.take b) := by
  induction b with
  | zero => omega
  | succ b ih =>
    have := bsum_take_succ l b (by omega)
    have := Char.utf8Size_pos l[b]
    by_cases a = b <;> grind

theorem bsum_take_le (l : List Char) {a b : Nat} (hab : a ≤ b) :
    bsum (l.take a) ≤ bsum (l.take b) := by
  induction l generalizing a b with
  | nil => simp
  | cons c l ih => cases a <;> cases b <;> grind [bsum]

theorem utf8GetAux_take (l : List Char) (i : String.Pos.Raw) (k : Nat) (h : k < l.length) :
    String.Pos.Raw.utf8GetAux l i ⟨i.byteIdx + bsum (l.take k)⟩ = l[k] := by
  induction l generalizing i k with
  | nil => simp at h
  | cons c l ih =>
    cases k with
    | zero => simp [String.Pos.Raw.utf8GetAux, bsum]
    | succ k =>
      have ih' := ih (i + c) k (by simpa using h)
      have := Char.utf8Size_pos c
      simp only [String.Pos.Raw.utf8GetAux, List.take_succ_cons, bsum, List.getElem_cons_succ]
      have hne : ¬ (i = ⟨i.byteIdx + (c.utf8Size + bsum (List.take k l))⟩) := by
        intro h; have := congrArg String.Pos.Raw.byteIdx h; simp at this; omega
      simp only [hne, ite_false]
      simpa [String.Pos.Raw.add_char_eq, Nat.add_assoc] using ih'

theorem get_off (s : String) (k : Nat) (h : k < s.toList.length) :
    (off s k).get s = s.toList[k] := by
  have := utf8GetAux_take s.toList 0 k h
  simpa [String.Pos.Raw.get, off] using this

theorem next_off (s : String) (k : Nat) (h : k < s.toList.length) :
    (off s k).next s = off s (k + 1) := by
  grind [String.Pos.Raw.next, get_off, off, bsum_take_succ, String.Pos.Raw.add_char_eq]

theorem walk_off (s : String) (k j : Nat) (h : k + j ≤ s.toList.length) :
    walk s (off s k) j = off s (k + j) := by
  induction j generalizing k <;> grind [walk, next_off]

theorem atEnd_off (s : String) (k : Nat) (h : k ≤ s.toList.length) :
    (off s k).atEnd s ↔ k = s.toList.length := by
  have := @bsum_take_lt s.toList k s.toList.length
  grind [String.Pos.Raw.atEnd, off, utf8ByteSize_eq]

theorem off_lt_off (s : String) {a b : Nat} (hb : b ≤ s.toList.length) :
    off s a < off s b ↔ a < b := by
  have := @bsum_take_le s.toList b a
  have := @bsum_take_lt s.toList a b
  grind [String.Pos.Raw.lt_iff, off]

/-! ## `positions` of `ofString` -/

/-- Index `j` starts a line: it is `0` or follows a newline. -/
def IsLineStart (cs : List Char) (j : Nat) : Prop := j = 0 ∨ cs[j - 1]? = some '\n'

theorem count_take_succ (l : List Char) (c : Char) (k : Nat) (h : k < l.length) :
    (l.take (k + 1)).count c = (l.take k).count c + (if l[k] = c then 1 else 0) := by
  rw [List.take_add_one, List.count_append, List.getElem?_eq_getElem h]
  simp [List.count_singleton]

def PInv (s : String) (ps : Array String.Pos.Raw) (k : Nat) : Prop :=
  ps.size = (s.toList.take k).count '\n' + 1 ∧
  ∀ idx (h : idx < ps.size), ∃ j, ps[idx] = off s j ∧ j ≤ k ∧ IsLineStart s.toList j ∧
    (s.toList.take j).count '\n' = idx

/-- `positions` holds the start of each line, followed by the end of the file. -/
def PosSpec (s : String) (ps : Array String.Pos.Raw) : Prop :=
  ps.size = s.toList.count '\n' + 2 ∧
  ps[ps.size - 1]! = off s s.toList.length ∧
  ∀ idx (h : idx < ps.size - 1), ∃ j, ps[idx] = off s j ∧ j ≤ s.toList.length ∧
    IsLineStart s.toList j ∧ (s.toList.take j).count '\n' = idx

theorem ofString_loop_positions (s : String) (i lineStart : String.Pos.Raw)
    (ps : Array String.Pos.Raw) (cps : Array (Thunk (Array ColumnCheckpoint))) :
    ∀ k, k ≤ s.toList.length → i = off s k → PInv s ps k →
      PosSpec s (FileMap.ofString.loop s i lineStart ps cps).positions := by
  fun_induction FileMap.ofString.loop s i lineStart ps cps with
  | case1 i lineStart ps cps hend =>
    intro k hk hi hinv
    have := (atEnd_off s k hk).1 (by grind)
    grind [PInv, PosSpec, List.take_length]
  | case2 i lineStart ps cps hend c next hnl ih =>
    intro k hk hi hinv
    have hkn : k < s.toList.length := by have := (atEnd_off s k hk).2; grind
    have := get_off s k hkn
    have := count_take_succ s.toList '\n' k hkn
    apply ih (k + 1) hkn (by grind [next_off])
    refine ⟨by grind [PInv], fun idx hidx => ?_⟩
    rw [Array.getElem_push]
    split
    · grind [PInv]
    · exact ⟨k + 1, by grind [next_off], by omega, Or.inr (by grind [List.getElem?_eq_getElem]),
        by grind [PInv]⟩
  | case3 i lineStart ps cps hend c next hnl ih =>
    intro k hk hi hinv
    have hkn : k < s.toList.length := by have := (atEnd_off s k hk).2; grind
    have := get_off s k hkn
    have := count_take_succ s.toList '\n' k hkn
    apply ih (k + 1) hkn (by grind [next_off])
    grind [PInv]

theorem ofString_positions (s : String) : PosSpec s (FileMap.ofString s).positions := by
  apply ofString_loop_positions s _ _ _ _ 0 (by omega) rfl
  refine ⟨by simp, ?_⟩
  intro idx hidx
  simp at hidx
  subst hidx
  exact ⟨0, rfl, by omega, Or.inl rfl, by simp⟩

/-! ## Lines as lists of characters -/

theorem count_take_mono (l : List Char) {a b : Nat} (h : a ≤ b) :
    (l.take a).count '\n' ≤ (l.take b).count '\n' :=
  (List.take_prefix_take_left h).count_le _

/-- A line start `j'` after a newline-free stretch `[j, k)` cannot lie inside it. -/
theorem lineStart_le (l : List Char) {j j' k : Nat}
    (hno : ∀ i, j ≤ i → i < k → l[i]? ≠ some '\n') (hls : IsLineStart l j') (hj'k : j' ≤ k) :
    j' ≤ j := by
  have := hno (j' - 1)
  grind [IsLineStart]

theorem count_take_eq_of_no_newline (l : List Char) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ l.length)
    (hno : ∀ i, j ≤ i → i < k → l[i]? ≠ some '\n') :
    (l.take k).count '\n' = (l.take j).count '\n' := by
  induction k with
  | zero => grind
  | succ k ih =>
    by_cases hjk' : j = k + 1
    · subst hjk'; rfl
    · have := count_take_succ l '\n' k (by omega)
      have := hno k (by omega) (by omega)
      have := ih (by omega) (by omega) (fun i h1 h2 => hno i h1 (by omega))
      grind

/-- The count of newlines before a line start increases at the preceding newline. -/
theorem count_take_lineStart (l : List Char) {j : Nat} (hj : 0 < j) (hjn : j ≤ l.length)
    (hls : IsLineStart l j) : (l.take j).count '\n' = (l.take (j - 1)).count '\n' + 1 := by
  have := count_take_succ l '\n' (j - 1) (by omega)
  rcases hls with h | h
  · omega
  · grind

theorem lineStart_unique (l : List Char) {j₁ j₂ : Nat} (h₁ : j₁ ≤ l.length) (h₂ : j₂ ≤ l.length)
    (hls₁ : IsLineStart l j₁) (hls₂ : IsLineStart l j₂)
    (hc : (l.take j₁).count '\n' = (l.take j₂).count '\n') : j₁ = j₂ := by
  have := @count_take_lineStart l j₁
  have := @count_take_lineStart l j₂
  have := @count_take_mono l j₁ (j₂ - 1)
  have := @count_take_mono l j₂ (j₁ - 1)
  grind [IsLineStart]

/-- Every prefix has a last line start. -/
theorem exists_lastLineStart (l : List Char) (k : Nat) (hk : k ≤ l.length) :
    ∃ j, j ≤ k ∧ IsLineStart l j ∧ ∀ i, j ≤ i → i < k → l[i]? ≠ some '\n' := by
  induction k with
  | zero => exact ⟨0, by omega, Or.inl rfl, by intros; omega⟩
  | succ k ih =>
    obtain ⟨j, h1, h2, h3⟩ := ih (by omega)
    by_cases hk' : l[k]? = some '\n'
    · exact ⟨k + 1, by omega, Or.inr (by simpa using hk'), by intros; omega⟩
    · refine ⟨j, by omega, h2, fun i hi1 hi2 => ?_⟩
      by_cases i = k
      · subst i; exact hk'
      · exact h3 i hi1 (by omega)

theorem exists_lineStart (s : String) (l : Nat) (h₁ : 1 ≤ l) (h₂ : l ≤ s.toList.count '\n' + 1) :
    ∃ j, j ≤ s.toList.length ∧ IsLineStart s.toList j ∧ (s.toList.take j).count '\n' = l - 1 := by
  obtain ⟨hsz, -, hps⟩ := ofString_positions s
  obtain ⟨j, -, h⟩ := hps (l - 1) (by omega)
  exact ⟨j, h⟩

/-! ## Specification of `lineStart` -/

theorem ofString_source (s : String) : (FileMap.ofString s).source = s := by
  suffices ∀ i lineStart ps cps, (FileMap.ofString.loop s i lineStart ps cps).source = s from
    this ..
  intro i lineStart ps cps
  fun_induction FileMap.ofString.loop s i lineStart ps cps <;> grind

/--
Line `l` (1-based) starts at the byte offset of the unique character index `j` that is `0` or
follows a newline and has `l - 1` newlines before it.
-/
theorem lineStart_ofString (s : String) (l : Nat) (h₁ : 1 ≤ l) (h₂ : l ≤ s.toList.count '\n' + 1)
    (j : Nat) (hj : j ≤ s.toList.length) (hls : IsLineStart s.toList j)
    (hc : (s.toList.take j).count '\n' = l - 1) :
    (FileMap.ofString s).lineStart l = off s j := by
  obtain ⟨hsz, -, hps⟩ := ofString_positions s
  obtain ⟨j', h1, h2, h3, h4⟩ := hps (l - 1) (by omega)
  have := lineStart_unique s.toList hj h2 hls h3 (by omega)
  grind [FileMap.lineStart]

/-! ## Specification of `codepointPosToUtf16Pos` -/

/-- Sum of the UTF-16 sizes of a list of characters. -/
def utf16Sum (l : List Char) : Nat := (l.map fun c => (Char.utf16Size c).toNat).sum

theorem aux_off (s : String) (col j acc : Nat) (h : j + col ≤ s.toList.length) :
    codepointPosToUtf16PosFromAux s col (off s j) acc =
      acc + utf16Sum ((s.toList.drop j).take col) := by
  induction col generalizing j acc with
  | zero => simp [codepointPosToUtf16PosFromAux, utf16Sum]
  | succ col ih =>
    have := List.drop_eq_getElem_cons (show j < s.toList.length by omega)
    grind [codepointPosToUtf16PosFromAux, next_off, get_off, utf16Sum]

/--
The UTF-16 column of codepoint `col` on line `l` (with `j` its start as in `lineStart_ofString`)
is the UTF-16 size of the `col` characters from `j` on.
-/
theorem codepointPosToUtf16Pos_ofString_spec (s : String) (l col : Nat) (h₁ : 1 ≤ l)
    (h₂ : l ≤ s.toList.count '\n' + 1)
    (j : Nat) (hls : IsLineStart s.toList j) (hc : (s.toList.take j).count '\n' = l - 1)
    (hcol : j + col ≤ s.toList.length) :
    (FileMap.ofString s).codepointPosToUtf16Pos l col = utf16Sum ((s.toList.drop j).take col) := by
  rw [codepointPosToUtf16Pos_ofString, codepointPosToUtf16Pos_empty,
    lineStart_ofString s l h₁ h₂ j (by omega) hls hc, ofString_source,
    codepointPosToUtf16PosFrom, aux_off s col j 0 hcol]
  omega

/-! ## Specification of `toPosition` -/

theorem off_inj (s : String) {a b : Nat} (ha : a ≤ s.toList.length) (hb : b ≤ s.toList.length)
    (h : off s a = off s b) : a = b := by
  have := off_lt_off s (a := a) hb
  have := off_lt_off s (a := b) ha
  grind [String.Pos.Raw.lt_iff]

theorem off_le_off (s : String) {a b : Nat} (ha : a ≤ s.toList.length) :
    off s a ≤ off s b ↔ a ≤ b := by
  have := off_lt_off s (a := b) ha
  have := @bsum_take_le s.toList a b
  grind [String.Pos.Raw.le_iff, String.Pos.Raw.lt_iff, off]

theorem toColumn_off (s : String) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ s.toList.length) :
    FileMap.toPosition.toColumn (off s k) s (off s j) 0 = k - j := by
  have := toColumn_walk (off s k) s (k - j) (off s j) 0 fun i hi => by
    rw [walk_off s j i (by omega)]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := off_inj s (by omega) hk h; omega
    · have := (atEnd_off s (j + i) (by omega)).1 h; omega
  rw [this, walk_off s j (k - j) (by omega), show j + (k - j) = k by omega,
    FileMap.toPosition.toColumn]
  simp

theorem toPosition_loop_spec (fm : FileMap) (s : String) (hps : PosSpec s fm.positions)
    (k j : Nat) (hk : k ≤ s.toList.length) (hjk : j ≤ k) (hls : IsLineStart s.toList j)
    (hno : ∀ i, j ≤ i → i < k → s.toList[i]? ≠ some '\n') (b e : Nat) (hbe : b < e)
    (he : e ≤ fm.positions.size - 1) (hb : fm.positions[b]! ≤ off s k)
    (he' : off s k < fm.positions[e]! ∨ e = fm.positions.size - 1) :
    FileMap.toPosition.loop { fm with columnCheckpoints := #[] } (off s k) s fm.positions b e =
      ⟨(s.toList.take k).count '\n' + 1, k - j⟩ := by
  obtain ⟨hsz, hlast, hspec⟩ := hps
  have hcnt := count_take_eq_of_no_newline s.toList hjk hk hno
  induction h : e - b using Nat.strongRecOn generalizing b e with
  | _ d ih =>
  rw [FileMap.toPosition.loop]
  split
  · -- `e = b + 1`: the line is `b`
    have hleaf : ∀ c : Bool, (if c then FileMap.toPosition.toColumn (off s k) s fm.positions[b]! 0
        else FileMap.toPosition.toColumn (off s k) s
          (({ fm with columnCheckpoints := #[] } : FileMap).findCheckpoint b (·.pos.byteIdx)
            (off s k).byteIdx).pos
          (({ fm with columnCheckpoints := #[] } : FileMap).findCheckpoint b (·.pos.byteIdx)
            (off s k).byteIdx).column) =
        FileMap.toPosition.toColumn (off s k) s fm.positions[b]! 0 := by
      have := lineStart_succ _ _ (show b < fm.positions.size by omega)
      intro c; cases c <;> simp [findCheckpoint_empty, this]
    simp only [hleaf]
    obtain ⟨jb, hjb1, hjb2, hjb3, hjb4⟩ := hspec b (by omega)
    have hb' : fm.positions[b]! = off s jb := by grind
    rw [hb'] at hb ⊢
    have hjbk := (off_le_off s hjb2).1 hb
    have hjbj := lineStart_le s.toList hno hjb3 hjbk
    have hlo := count_take_mono s.toList hjbj
    have hhi : (s.toList.take j).count '\n' ≤ b := by
      by_cases hel : e = fm.positions.size - 1
      · have := count_take_mono s.toList (a := j) (b := s.toList.length) (by omega)
        simp only [List.take_length] at this
        omega
      · obtain ⟨je, hje1, hje2, hje3, hje4⟩ := hspec e (by omega)
        have he'' : fm.positions[e]! = off s je := by
          grind
        have hkje : k < je := by
          rcases he' with h' | h'
          · rw [he''] at h'; exact (off_lt_off s hje2).1 h'
          · omega
        have := count_take_lineStart s.toList (j := je) (by omega) hje2 hje3
        have := count_take_mono s.toList (a := j) (b := je - 1) (by omega)
        omega
    have := lineStart_unique s.toList hjb2 (by omega) hjb3 hls (by omega)
    subst this
    simp only [toColumn_off s hjk hk, FileMap.getLine, FileMap.getLastLine]
    congr 1
    omega
  · obtain ⟨jm, hjm1, hjm2, hjm3, hjm4⟩ := hspec ((b + e) / 2) (by omega)
    have hm : fm.positions[(b + e) / 2]! = off s jm := by
      rw [getElem!_pos fm.positions _ (by omega)]; exact hjm1
    simp only [hm]
    split
    · rename_i heq
      have := off_inj s hk hjm2 (by simpa using heq)
      subst this
      have := lineStart_le s.toList hno hjm3 (Nat.le_refl _)
      simp only [FileMap.getLine, FileMap.getLastLine]
      congr 1 <;> omega
    · rename_i hne
      split
      · rename_i hgt
        refine ih (e - (b + e) / 2) (by omega) ((b + e) / 2) e (by omega) he ?_ he' rfl
        rw [hm]
        exact (off_le_off s hjm2).2 (Nat.le_of_lt ((off_lt_off s hk).1 hgt))
      · rename_i hngt
        refine ih ((b + e) / 2 - b) (by omega) b ((b + e) / 2) (by omega) (by omega) hb
          (Or.inl ?_) rfl
        rw [hm]
        have h1 : k ≠ jm := fun h => hne (by simp [h])
        have h2 : ¬ jm < k := fun h => hngt ((off_lt_off s hk).2 h)
        exact (off_lt_off s hjm2).2 (by omega)

theorem toPosition_ofString_of_lineStart (s : String) (k j : Nat) (hk : k ≤ s.toList.length)
    (hjk : j ≤ k)
    (hls : IsLineStart s.toList j) (hno : ∀ i, j ≤ i → i < k → s.toList[i]? ≠ some '\n') :
    (FileMap.ofString s).toPosition (off s k) = ⟨(s.toList.take k).count '\n' + 1, k - j⟩ := by
  rw [toPosition_ofString]
  have hps := ofString_positions s
  have hsz := hps.1
  have hlast := hps.2.1
  have hloop := toPosition_loop_spec (FileMap.ofString s) s hps k j hk hjk hls hno 0
    ((FileMap.ofString s).positions.size - 1) (by omega) (by omega)
    (by
      obtain ⟨j0, h1, h2, h3, h4⟩ := hps.2.2 0 (by omega)
      have := lineStart_unique s.toList h2 (Nat.zero_le _) h3 (Or.inl rfl) (by simpa using h4)
      subst this
      rw [getElem!_pos _ _ (by omega), h1]
      exact (off_le_off s (by omega)).2 (Nat.zero_le _))
    (Or.inr rfl)
  have hback : (FileMap.ofString s).positions.back! = off s s.toList.length := by
    rw [← hlast]; rfl
  have hle : off s k ≤ off s s.toList.length := (off_le_off s hk).2 hk
  simp only [FileMap.toPosition, ofString_source, hback]
  have hcond : (decide ((FileMap.ofString s).positions.size ≥ 2) &&
      decide (off s k ≤ off s s.toList.length)) = true := by simp [hle]; omega
  simp only [hcond, ↓reduceIte]
  rw [ofString_source] at hloop
  exact hloop

/-- The number of characters after the last newline in `l`. -/
def column (l : List Char) : Nat := (l.reverse.takeWhile (· ≠ '\n')).length

theorem column_append_singleton (l : List Char) (c : Char) :
    column (l ++ [c]) = if c = '\n' then 0 else column l + 1 := by
  by_cases h : c = '\n' <;> simp [column, h]

theorem column_take (l : List Char) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ l.length)
    (hls : IsLineStart l j) (hno : ∀ i, j ≤ i → i < k → l[i]? ≠ some '\n') :
    column (l.take k) = k - j := by
  induction k with
  | zero => simp [column]
  | succ k ih =>
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      column_append_singleton]
    by_cases hjk' : j = k + 1
    · have : l[k] = '\n' := by grind [IsLineStart]
      simp [this]; omega
    · have := hno k (by omega) (by omega)
      have := ih (by omega) (by omega) (fun i h1 h2 => hno i h1 (by omega))
      grind

/--
The position of character index `k` is its line, one more than the number of newlines before it,
and its column, the number of characters since the last newline before it.
-/
theorem toPosition_ofString_spec (s : String) (k : Nat) (hk : k ≤ s.toList.length) :
    (FileMap.ofString s).toPosition (off s k) =
      ⟨(s.toList.take k).count '\n' + 1, column (s.toList.take k)⟩ := by
  obtain ⟨j, hjk, hls, hno⟩ := exists_lastLineStart s.toList k hk
  rw [toPosition_ofString_of_lineStart s k j hk hjk hls hno, column_take s.toList hjk hk hls hno]

end FileMapCheckpoints
