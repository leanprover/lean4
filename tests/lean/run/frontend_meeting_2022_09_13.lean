import Lean

/-
(1) How are the source information, comments etc stored in the Syntax tree? In particular, how can one recreate the original source?
-/

elab "#reprint" e:term : command => do
  let some val := e.raw.reprint | throwError "failed to reprint"
  IO.println val

#reprint
  let x : Nat := 3 -- My comment 1
  x + 2 /- another comment here -/

elab "#repr" e:term : command => do
  IO.println (repr e)

#check Lean.SourceInfo

#repr
  let x : Nat := 3 -- My comment 1
  x + 2 /- another comment here -/

/-
(2) I am comfortable with the usual token level parsers but could not understand the code for `commentBody` and such parsers. How does one parse at character level?

-/

section
open Lean Parser
partial def commandCommentBodyFn (c : ParserContext) (s : ParserState) : ParserState :=
  go s
where
  go (s : ParserState) : ParserState := Id.run do
    let input := c.input
    let i     := s.pos
    if input.atEnd i then return s.mkUnexpectedError "unterminated command comment"
    let curr := input.get i
    let i    := input.next i
    if curr != '-' then return go (s.setPos i)
    let curr := input.get i
    let i    := input.next i
    if curr != '/' then return go (s.setPos i)
    let curr := input.get i
    let i    := input.next i
    if curr != '/' then return go (s.setPos i)
    -- Found '-//'
    return s.setPos i

def commandCommentBody : Parser :=
  { fn := rawFn commandCommentBodyFn (trailingWs := true) }

@[combinator_parenthesizer commandCommentBody] def commandCommentBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter commandCommentBody] def commandCommentBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

@[command_parser] def commandComment := leading_parser "//-" >> commandCommentBody >> ppLine

end

open Lean Elab Command in
@[command_elab commandComment] def elabCommandComment : CommandElab := fun stx => do
   let .atom _ val := stx[1] | return ()
   let str := val.extract 0 (val.endPos - ⟨3⟩)
   IO.println s!"str := {repr str}"

//- My command comment hello world -//

/-
(3) How does one split a `tacticSeq` into individual tactics, with the goal of running them one by one logging state along the way?
-/
section
open Lean Parser Elab Tactic

def getTactics (s : TSyntax ``tacticSeq) : Array (TSyntax `tactic) :=
  match s with
  | `(tacticSeq| { $[$t]* }) => t
  | `(tacticSeq| $[$t]*) => t
  | _ => #[]

elab "seq" s:tacticSeq : tactic => do
  -- IO.println s
  let tacs := getTactics s
  for tac in tacs do
    let gs ← getUnsolvedGoals
    withRef tac <| addRawTrace (goalsToMessageData gs)
    evalTactic tac

example (h : x = y) : 0 + x = y := by
  seq rw [h]; rw [Nat.zero_add]
  done

example (h : x = y) : 0 + x = y := by
  seq rw [h]
      rw [Nat.zero_add]
  done

example (h : x = y) : 0 + x = y := by
  seq { rw [h]; rw [Nat.zero_add] }
  done

end

/-
(4) Related to the above, how does one parse and run all the commands in a file updating the environment, with modifications to the running in some cases (specifically when running a `tacticSeq` log state at each step)?
-/

#check Lean.Elab.runFrontend
