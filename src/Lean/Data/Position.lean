/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import Lean.ToExpr

public section

namespace Lean

structure Position where
  line   : Nat
  column : Nat
  deriving Inhabited, DecidableEq, Repr, ToJson, FromJson

namespace Position
protected def lt : Position → Position → Bool
  | ⟨l₁, c₁⟩, ⟨l₂, c₂⟩ => Prod.lexLt (l₁, c₁) (l₂, c₂)

instance : ToFormat Position :=
  ⟨fun ⟨l, c⟩ => "⟨" ++ format l ++ ", " ++ format c ++ "⟩"⟩

instance : ToString Position :=
  ⟨fun ⟨l, c⟩ => "⟨" ++ toString l ++ ", " ++ toString c ++ "⟩"⟩

instance : ToExpr Position where
  toExpr p   := mkAppN (mkConst ``Position.mk) #[toExpr p.line, toExpr p.column]
  toTypeExpr := mkConst ``Position

end Position

/-- Returns the number of bytes required to encode this `Char` in UTF-16. -/
def Char.utf16Size (c : Char) : UInt32 :=
  if c.val ≤ 0xFFFF then 1 else 2

private def String.codepointPosToUtf16PosFromAux (s : String) : Nat → String.Pos.Raw → Nat → Nat
  | 0,    _,       utf16pos => utf16pos
  | cp+1, utf8pos, utf16pos =>
    codepointPosToUtf16PosFromAux s cp (utf8pos.next s)
      (utf16pos + (Char.utf16Size (utf8pos.get s)).toNat)

/-- Computes the UTF-16 offset of the `n`-th Unicode codepoint
in the substring of `s` starting at UTF-8 offset `off`.
Yes, this is actually useful.-/
def String.codepointPosToUtf16PosFrom (s : String) (n : Nat) (off : String.Pos.Raw) : Nat :=
  codepointPosToUtf16PosFromAux s n off 0

/-- The columns of a position inside of a long line, see `FileMap.columnCheckpoints`. -/
private structure ColumnCheckpoint where
  /-- The position of a character on the line. -/
  pos         : String.Pos.Raw
  /-- The number of codepoints between the start of the line and `pos`. -/
  column      : Nat
  /-- The number of UTF-16 code units between the start of the line and `pos`. -/
  utf16Column : Nat
  deriving Inhabited

/-- Content of a file together with precalculated positions of newlines. -/
structure FileMap where
  /-- The content of the file. -/
  source    : String
  /-- The positions of newline characters.
  The first entry is always `0` and the last always the index of the last character.
  In particular, if the last character is a newline, that index will appear twice. -/
  positions : Array String.Pos.Raw
  /--
  For each line, positions on it at least `FileMap.columnCheckpointInterval` bytes apart from each
  other and from the start of the line. They bound the work needed for computing a column, and are
  only computed for a line once a column on it is needed.
  -/
  private columnCheckpoints : Array (Thunk (Array ColumnCheckpoint))
  deriving Inhabited

class MonadFileMap (m : Type → Type) where
  getFileMap : m FileMap

export MonadFileMap (getFileMap)

namespace FileMap

/-- The last line should always be `positions.size - 1`. -/
def getLastLine (fmap : FileMap) : Nat :=
  fmap.positions.size - 1

/-- The line numbers associated with the `positions` of the `FileMap`.
`fmap.getLine i` is the iᵗʰ entry of `#[1, 2, …, n-1, n-1]`
where `n` is the `size` of `positions`. -/
def getLine (fmap : FileMap) (x : Nat) : Nat :=
  min (x + 1) fmap.getLastLine

/-- The minimal distance in bytes between the checkpoints of a line, see `columnCheckpoints`. -/
private def columnCheckpointInterval : Nat := 256

/-- Returns the checkpoints of the line from `lineStart` to `lineEnd`. -/
private def lineCheckpoints (s : String) (lineStart lineEnd : String.Pos.Raw) :
    Thunk (Array ColumnCheckpoint) :=
  if lineEnd.byteIdx - lineStart.byteIdx ≤ columnCheckpointInterval then .pure #[]
  else .mk fun _ => loop lineStart lineStart 0 0 #[]
where
  loop (i last : String.Pos.Raw) (column utf16Column : Nat) (cps : Array ColumnCheckpoint) :
      Array ColumnCheckpoint :=
    if i < lineEnd then
      let checkpoint := i.byteIdx - last.byteIdx ≥ columnCheckpointInterval
      loop (i.next s) (if checkpoint then i else last) (column + 1)
        (utf16Column + (Char.utf16Size (i.get s)).toNat)
        (if checkpoint then cps.push { pos := i, column, utf16Column } else cps)
    else
      cps
  termination_by lineEnd.byteIdx - i.byteIdx
  decreasing_by
    have := String.Pos.Raw.byteIdx_lt_byteIdx_next s i
    simp [String.Pos.Raw.lt_iff] at *
    omega

def ofString (s : String) : FileMap :=
  let rec loop (i lineStart : String.Pos.Raw) (ps : Array String.Pos.Raw)
      (cps : Array (Thunk (Array ColumnCheckpoint))) : FileMap :=
    if i.atEnd s then
      { source := s, positions := ps.push i
        columnCheckpoints := cps.push (lineCheckpoints s lineStart i) }
    else
      let c := i.get s
      let next := i.next s
      if c == '\n' then loop next next (ps.push next) (cps.push (lineCheckpoints s lineStart next))
      else loop next lineStart ps cps
  termination_by s.utf8ByteSize - i.byteIdx
  decreasing_by
    all_goals
      have := String.Pos.Raw.byteIdx_lt_byteIdx_next s i
      simp [String.Pos.Raw.atEnd] at *
      omega
  loop 0 0 #[0] #[]

/--
Returns the position of the start of (1-based) line `line`.
This gives the same result as `map.ofPosition ⟨line, 0⟩`, but is more efficient.
-/
def lineStart (map : FileMap) (line : Nat) : String.Pos.Raw :=
  if h : line - 1 < map.positions.size then
    map.positions[line - 1]
  else map.positions.back?.getD 0

/-- Returns whether (0-based) line `line` is too short to have checkpoints. -/
private def lineIsShort (fmap : FileMap) (line : Nat) : Bool :=
  match fmap.positions[line]?, fmap.positions[line + 1]? with
  | some lineStart, some lineEnd => lineEnd.byteIdx - lineStart.byteIdx ≤ columnCheckpointInterval
  | _, _ => true

/--
Returns the last checkpoint of (0-based) line `line` whose `key` is at most `x`, or the start of the
line if there is none. `key` must be monotone on the checkpoints of the line.
-/
@[specialize] private def findCheckpoint (fmap : FileMap) (line : Nat)
    (key : ColumnCheckpoint → Nat) (x : Nat) : ColumnCheckpoint :=
  let cps := (fmap.columnCheckpoints[line]?.map (·.get)).getD #[]
  loop cps 0 cps.size
where
  -- `key` is at most `x` before `lo` and greater from `hi` on
  @[specialize] loop (cps : Array ColumnCheckpoint) (lo hi : Nat) : ColumnCheckpoint :=
    if lo < hi then
      let mid := (lo + hi) / 2
      if key cps[mid]! ≤ x then loop cps (mid + 1) hi else loop cps lo mid
    else if lo == 0 then { pos := fmap.lineStart (line + 1), column := 0, utf16Column := 0 }
    else cps[lo - 1]!
  termination_by hi - lo

def toPosition (fmap : FileMap) (pos : String.Pos.Raw) : Position :=
  match fmap with
  | { source := str, positions := ps, .. } =>
    if ps.size >= 2 && pos <= ps.back! then
      let rec toColumn (i : String.Pos.Raw) (c : Nat) : Nat :=
        if i == pos || i.atEnd str then c
        else toColumn (i.next str) (c+1)
      termination_by str.utf8ByteSize - i.byteIdx
      decreasing_by
        have := String.Pos.Raw.byteIdx_lt_byteIdx_next str i
        simp [String.Pos.Raw.atEnd] at *
        omega
      let rec loop (b e : Nat) :=
        if e ≤ b + 1 then
          let column :=
            if fmap.lineIsShort b then
              toColumn ps[b]! 0
            else
              let cp := fmap.findCheckpoint b (·.pos.byteIdx) pos.byteIdx
              toColumn cp.pos cp.column
          { line := fmap.getLine b, column }
        else
          let m := (b + e) / 2;
          let posM := ps[m]!
          if pos == posM then { line := fmap.getLine m, column := 0 }
          else if pos > posM then loop m e
          else loop b m
      termination_by e - b
      loop 0 (ps.size - 1)
    else if ps.isEmpty then
      ⟨0, 0⟩
    else
      -- Some systems like the delaborator use synthetic positions without an input file,
      -- which would violate `toPositionAux`'s invariant.
      -- Can also happen with EOF errors, which are not strictly inside the file.
      ⟨fmap.getLastLine, ps.back!.byteDistance pos⟩

/-- Convert a `Lean.Position` to a `String.Pos`. -/
def ofPosition (text : FileMap) (pos : Position) : String.Pos.Raw :=
  let colPos :=
    if h : pos.line - 1 < text.positions.size then
      text.positions[pos.line - 1]
    else if text.positions.isEmpty then
      0
    else
      text.positions.back!
  (text.source.pos! colPos).nextn pos.column |>.offset

/-- Computes the UTF-16 offset of codepoint `col` of (1-based) line `line`. -/
def codepointPosToUtf16Pos (fmap : FileMap) (line col : Nat) : Nat :=
  if fmap.lineIsShort (line - 1) then
    String.codepointPosToUtf16PosFrom fmap.source col (fmap.lineStart line)
  else
    let cp := fmap.findCheckpoint (line - 1) (·.column) col
    cp.utf16Column + String.codepointPosToUtf16PosFrom fmap.source (col - cp.column) cp.pos

end FileMap
end Lean

def Lean.String.toFileMap (s : String) : Lean.FileMap :=
  Lean.FileMap.ofString s
