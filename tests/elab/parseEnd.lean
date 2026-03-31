import Lean.Elab.Command

open Lean Elab Command Parser

declare_syntax_cat balanced
syntax "!" : balanced
syntax "(" balanced* ")" : balanced


elab d:docComment "test" : command => do
  let some ⟨pos, endPos⟩ := d.raw[1].getRange? (canonicalOnly := true)
    | throwErrorAt d "Docstring doesn't have a canonical position"
  let p := Parser.categoryParser `balanced 0
  let p := andthenFn whitespace p.fn
  let text ← getFileMap
  let input := text.source

  let endPos := input.prev <| input.prev endPos

  if h : endPos ≤ input.rawEndPos then
    let ictx := mkInputContext input (← getFileName) (endPos := endPos) (endPos_valid := h)
    let env ← getEnv
    let s := { mkParserState input with pos }
    let s := p.run ictx { env, options := {} } (getTokenTable env) s
    if !s.allErrors.isEmpty then
      for (pos, _, err) in s.allErrors do
        logMessage {
          fileName := (← getFileName )
          pos := text.toPosition pos
          endPos := some (text.toPosition endPos)
          data := s!"{err.toString}"
        }
    else if ictx.atEnd s.pos then
      logInfo s.stxStack.back
    else
        let pos := s.pos
        logMessage {
          fileName := (← getFileName )
          pos := text.toPosition pos
          endPos := some (text.toPosition endPos)
          data := s!"expected end of input"
        }
  else
    throwError "Out of bounds"


/-- info: (!!(!)) -/
#guard_msgs in
/--
( ! ! (!) )
-/
test

/-- error: unexpected end of input; expected ')' -/
#guard_msgs in
/--
(
-/
test
