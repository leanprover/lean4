import Lean

new_frontend

namespace Lean.Parser

def strInterpolantStrLitKind := `strInterpolantStrLitKind
def strInterpolantKind := `strInterpolantKind

def isQuotableCharForStrInterpolant (c : Char) : Bool :=
c == '{' || isQuotableCharDefault c

partial def strInterpolantFn (p : ParserFn) : ParserFn :=
fun c s =>
let input     := c.input
let stackSize := s.stackSize
let rec parse (startPos : Nat) (c : ParserContext) (s : ParserState) : ParserState :=
  let i     := s.pos
  if input.atEnd i then
    s.mkEOIError
  else
    let curr := input.get i
    let s    := s.setPos (input.next i)
    if curr == '\"' then
      let s := mkNodeToken strInterpolantStrLitKind startPos c s
      s.mkNode strInterpolantKind stackSize
    else if curr == '\\' then
      andthenFn (quotedCharCoreFn isQuotableCharForStrInterpolant) (parse startPos) c s
    else if curr == '{' then
      let s := mkNodeToken strInterpolantStrLitKind startPos c s
      let s := p c s
      if s.hasError then s
      else
        let pos := s.pos
        andthenFn (satisfyFn (· == '}') "expected '}'") (parse pos) c s
    else
      parse startPos c s
let startPos := s.pos
if input.atEnd startPos then
  s.mkEOIError
else
  let s := s.next input startPos
  parse startPos c s

@[inline] def strInterpolantNoAntiquot (p : Parser) : Parser :=
{ fn   := strInterpolantFn p.fn,
  info := mkAtomicInfo "strInterpolant" }

def strInterpolant (p : Parser) : Parser :=
withAntiquot (mkAntiquot "strInterpolant" strInterpolantKind) $ strInterpolantNoAntiquot p

end Lean.Parser

namespace Lean.PrettyPrinter.Formatter

@[combinatorFormatter Lean.Parser.strInterpolant]
def strInterpolant.formatter (p : Formatter) : Formatter :=
throwError "NIY"

end Lean.PrettyPrinter.Formatter

namespace Lean.PrettyPrinter.Parenthesizer

@[combinatorParenthesizer Lean.Parser.strInterpolant]
def strInterpolant.parenthesizer (p : Parenthesizer) : Parenthesizer :=
throwError "NIY"

end Lean.PrettyPrinter.Parenthesizer

namespace Lean.Syntax

def decodeStrInterpolantQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) :=
match decodeQuotedChar s i with
| some r => some r
| none   =>
  let c := s.get i
  let i := s.next i
  if c == '{' then pure ('{', i)
  else none

partial def decodeStrInterpolantStrLit (s : String) : Option String :=
let rec loop (i : String.Pos) (acc : String) :=
  let c := s.get i
  let i := s.next i
  if c == '\"' || c == '{' then
    pure acc
  else if s.atEnd i then
    none
  else if c == '\\' then do
    let (c, i) ← decodeStrInterpolantQuotedChar s i
    loop i (acc.push c)
  else
    loop i (acc.push c)
loop 1 ""

partial def isStrInterpolantStrLit? (stx : Syntax) : Option String :=
match isLit? Parser.strInterpolantStrLitKind stx with
| none     => none
| some val => decodeStrInterpolantStrLit val

def expandStrInterpolantChunks (chunks : Array Syntax) (mkAppend : Syntax → Syntax → MacroM Syntax) (mkElem : Syntax → MacroM Syntax) : MacroM Syntax :=
chunks.iterateM Syntax.missing fun i elem result => do
  let elem ← (match elem.isStrInterpolantStrLit? with
    | none     => mkElem elem
    | some str => mkElem (mkStxStrLit str))
  -- TODO: remove `(` after we write new elabDo
  (if i.val == 0 then pure elem else mkAppend result elem)

end Lean.Syntax

namespace Lean.Parser.Term

@[termParser] def toString := parser!:leadPrec "toString! " >> strInterpolant termParser

end Lean.Parser.Term

open Lean

def mkToString! (chunks : Array Syntax) : MacroM Syntax :=
Syntax.expandStrInterpolantChunks chunks (fun a b => `($a ++ $b)) (fun a => `(toString $a))

macro_rules[Lean.Parser.Term.toString]
| `(toString! $strInterp) => mkToString! strInterp.getArgs

#eval let x := 10 toString! "hello { x + 10 } world"
#eval toString! "{1+1}"
#eval toString! "{1}+{1}"
#eval toString! "\{{1+1}}"
#eval toString! "a{1}"

def g (x : Nat) : StateRefT Nat IO Nat := do
modify (· + x)
get

def ex : StateRefT Nat IO Unit := do
IO.println $ toString! ">> hello {(←g 1)}"
IO.println $ toString! ">> world {(←g 1)}"
pure ()

#eval ex.run' 0

-- We can safely use string interpolation in macros
macro valueOf! x:term : term =>
  let s := quote (toString x.prettyPrint)
  `((do { let s := $s; let r := $x; IO.println (toString! "value of ({$s}) = {r}"); pure r } : IO _))

#eval let s := 10; valueOf! s+2
