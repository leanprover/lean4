structure Position :=
(line   : Nat := 1)
(column : Nat := 0)

instance : Inhabited Position :=
⟨{}⟩

structure FileMap :=
(source    : String)
(positions : Array String.Pos)
(lines     : Array Nat)

namespace FileMap

instance : Inhabited FileMap :=
⟨{ source := "", positions := Array.empty, lines := Array.empty }⟩

private partial def ofStringAux (s : String) : String.Pos → Nat → Array String.Pos → Array Nat → FileMap
| i line ps lines :=
  if s.atEnd i then { source := s, positions := ps.push i, lines := lines.push line }
  else
    let c := s.get i in
    let i := s.next i in
    if c == '\n' then ofStringAux i (line+1) (ps.push i) (lines.push (line+1))
    else ofStringAux i line ps lines

def ofString (s : String) : FileMap :=
ofStringAux s 0 1 (Array.empty.push 0) (Array.empty.push 1)

private partial def toColumnAux (str : String) (lineBeginPos : String.Pos) (pos : String.Pos) : String.Pos → Nat → Nat
| i c :=
  if i == pos || str.atEnd i then c
  else toColumnAux (str.next i) (c+1)

/- Remark: `pos` is in `[ps.get b, ps.get e]` and `b < e` -/
private partial def toPositionAux (str : String) (ps : Array Nat) (lines : Array Nat) (pos : String.Pos) : Nat → Nat → Position
| b e :=
  let posB := ps.get b in
  if e == b + 1 then { line := lines.get b, column := toColumnAux str posB pos posB 0 }
  else
    let m := (b + e) / 2 in
    let posM := ps.get m in
    if pos == posM then { line := lines.get m, column := 0 }
    else if pos > posM then toPositionAux m e
    else toPositionAux b m

def toPosition : FileMap → String.Pos → Position
| { source := str, positions := ps, lines := lines } pos := toPositionAux str ps lines pos 0 (ps.size-1)

end FileMap

def String.toFileMap (s : String) : FileMap :=
FileMap.ofString s

partial def showLineColsAux (fmap : FileMap) : String.Pos → IO Unit
| i :=
  if fmap.source.atEnd i then pure ()
  else do
    let p := fmap.toPosition i,
    IO.println ("[" ++ toString i ++ "] := (" ++ toString p.line ++ ", " ++ toString p.column ++ ")"),
    showLineColsAux (fmap.source.next i)

def showLineCols (str : String) : IO Unit :=
let fmap := FileMap.ofString str in
IO.println ("string: " ++ repr str) *>
showLineColsAux fmap 0

def main (xs : List String) : IO Unit :=
do
  showLineCols ("hello\nwoαld\ntβst"),
  showLineCols "",
  showLineCols "\n\n\n",
  showLineCols "\n\n\nabc\n",
  showLineCols "\n\n\nabc"
