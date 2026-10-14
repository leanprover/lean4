module
import all Lean.Data.Position

/-!
Proves that the per-line column checkpoints of `FileMap` (#15646) do not change the results of
`FileMap.toPosition` and `FileMap.codepointPosToUtf16Pos`: for every string, both functions return
the same on `FileMap.ofString s` as on the same map without checkpoints.

`ofString` records each checkpoint after walking `column` characters with `String.Pos.Raw.next` from
the start of its line (`Valid`), and both lookups only ever resume such a walk from a checkpoint they
found on the same line. The proofs therefore never reason about UTF-8 itself.
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
      ∃ h : line < fm.columnCheckpoints.size, ∃ k, ∃ h' : k < fm.columnCheckpoints[line].size,
        fm.findCheckpoint line key x = fm.columnCheckpoints[line][k] ∧
        key fm.columnCheckpoints[line][k] ≤ x := by
  have := findCheckpoint_loop_sound fm line key x (fm.columnCheckpoints[line]?.getD #[]) 0
    (fm.columnCheckpoints[line]?.getD #[]).size (by simp) (by simp)
  by_cases hl : line < fm.columnCheckpoints.size <;> grind [FileMap.findCheckpoint]

/-! ## Validity of the checkpoints computed by `ofString` -/

/-- `cp` is the checkpoint reached by walking from the line start `ls`. -/
def Valid (s : String) (ls : String.Pos.Raw) (cp : ColumnCheckpoint) : Prop :=
  cp.pos = walk s ls cp.column ∧
  cp.utf16Column = codepointPosToUtf16PosFromAux s cp.column ls 0 ∧
  cp.pos.byteIdx < s.utf8ByteSize

def _root_.Lean.FileMap.WF (fm : FileMap) : Prop :=
  fm.columnCheckpoints.size < fm.positions.size ∧
  ∀ b (hb : b < fm.columnCheckpoints.size), ∀ cp ∈ fm.columnCheckpoints[b],
    Valid fm.source fm.positions[b]! cp

def LoopInv (s : String) (i : String.Pos.Raw) (column u : Nat) (lineCps : Array ColumnCheckpoint)
    (ps : Array String.Pos.Raw) (cps : Array (Array ColumnCheckpoint)) : Prop :=
  ps.size = cps.size + 1 ∧
  i = walk s ps[cps.size]! column ∧
  u = codepointPosToUtf16PosFromAux s column ps[cps.size]! 0 ∧
  (∀ cp ∈ lineCps, Valid s ps[cps.size]! cp) ∧
  (∀ b (hb : b < cps.size), ∀ cp ∈ cps[b], Valid s ps[b]! cp)

theorem valid_step (s : String) (i : String.Pos.Raw) (column u : Nat)
    (lineCps : Array ColumnCheckpoint) (ps : Array String.Pos.Raw)
    (cps : Array (Array ColumnCheckpoint)) (checkpoint : Prop) [Decidable checkpoint]
    (hend : ¬ i.atEnd s = true) (hi : i = walk s ps[cps.size]! column)
    (hu : u = codepointPosToUtf16PosFromAux s column ps[cps.size]! 0)
    (hl : ∀ cp ∈ lineCps, Valid s ps[cps.size]! cp) :
    ∀ cp ∈ (if checkpoint then lineCps.push { pos := i, column, utf16Column := u } else lineCps),
      Valid s ps[cps.size]! cp := by
  grind [Valid, String.Pos.Raw.atEnd]

theorem ofString_loop_wf (s : String) (i last : String.Pos.Raw) (column u : Nat)
    (lineCps : Array ColumnCheckpoint) (ps : Array String.Pos.Raw)
    (cps : Array (Array ColumnCheckpoint)) (h : LoopInv s i column u lineCps ps cps) :
    (FileMap.ofString.loop s i last column u lineCps ps cps).WF := by
  fun_induction FileMap.ofString.loop s i last column u lineCps ps cps with
  | case1 => grind [FileMap.WF, LoopInv]
  | case2 i last column u lineCps ps cps hend c next checkpoint lineCps' hnl ih =>
    have := valid_step s _ _ _ _ _ _ checkpoint hend h.2.1 h.2.2.1 h.2.2.2.1
    grind [LoopInv, walk, codepointPosToUtf16PosFromAux]
  | case3 i last column u lineCps ps cps hend c next checkpoint last' lineCps' hnl ih =>
    have := valid_step s _ _ _ _ _ _ checkpoint hend h.2.1 h.2.2.1 h.2.2.2.1
    grind [LoopInv, walk_succ, aux_add, codepointPosToUtf16PosFromAux]

theorem ofString_wf (s : String) : (FileMap.ofString s).WF :=
  ofString_loop_wf s _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, by simp, by simp⟩

/-! ## Main theorems -/

theorem lineStart_succ (fm : FileMap) (b : Nat) (hb : b < fm.positions.size) :
    fm.lineStart (b + 1) = fm.positions[b]! := by
  grind [FileMap.lineStart]

theorem findCheckpoint_empty (fm : FileMap) (line : Nat) (key : ColumnCheckpoint → Nat) (x : Nat) :
    ({ fm with columnCheckpoints := #[] } : FileMap).findCheckpoint line key x =
      { pos := fm.lineStart (line + 1), column := 0, utf16Column := 0 } := by
  grind [FileMap.findCheckpoint, FileMap.findCheckpoint.loop, FileMap.lineStart]

theorem codepointPosToUtf16Pos_eq (fm : FileMap) (hwf : fm.WF) (line col : Nat) :
    fm.codepointPosToUtf16Pos line col =
      { fm with columnCheckpoints := #[] }.codepointPosToUtf16Pos line col := by
  simp only [FileMap.codepointPosToUtf16Pos, findCheckpoint_empty]
  rcases findCheckpoint_sound fm (line - 1) (·.column) col with h | ⟨hb, k, hk, h, hle⟩
  · rw [h]
  · have := aux_add fm.source fm.columnCheckpoints[line - 1][k].column
      (col - fm.columnCheckpoints[line - 1][k].column) fm.positions[line - 1]! 0
    have := hwf.2 (line - 1) hb _ (Array.getElem_mem hk)
    grind [Valid, FileMap.WF, lineStart_succ, aux_shift, codepointPosToUtf16PosFrom]

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
    have := toColumn_walk pos fm.source fm.columnCheckpoints[b][k].column fm.positions[b]! 0
      fun j hj => by have := walk_lt fm.source fm.positions[b]! hj; grind [Valid, String.Pos.Raw.atEnd]
    grind [Valid, FileMap.WF, lineStart_succ]

theorem toPosition_loop_eq (fm : FileMap) (hwf : fm.WF) (pos : String.Pos.Raw)
    (ps : Array String.Pos.Raw) (b e : Nat) :
    FileMap.toPosition.loop fm pos fm.source ps b e =
      FileMap.toPosition.loop { fm with columnCheckpoints := #[] } pos fm.source ps b e := by
  induction h : e - b using Nat.strongRecOn generalizing b e with
  | _ n ih =>
  rw [FileMap.toPosition.loop, FileMap.toPosition.loop]
  have := toColumn_findCheckpoint fm hwf pos b
  split
  · grind [FileMap.getLine, FileMap.getLastLine]
  · have := ih (e - (b + e) / 2) (by omega) ((b + e) / 2) e rfl
    have := ih ((b + e) / 2 - b) (by omega) b ((b + e) / 2) rfl
    grind [FileMap.getLine, FileMap.getLastLine]

theorem toPosition_eq (fm : FileMap) (hwf : fm.WF) (pos : String.Pos.Raw) :
    fm.toPosition pos = { fm with columnCheckpoints := #[] }.toPosition pos := by
  have := toPosition_loop_eq fm hwf pos fm.positions
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

end FileMapCheckpoints
