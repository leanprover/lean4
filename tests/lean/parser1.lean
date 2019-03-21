import init.Lean.frontend init.IO
open Lean
open Lean.Parser
open Lean.Expander
open Lean.Elaborator

def checkReprint (p : List moduleParserOutput) (s : String) : ExceptT String IO Unit :=
do let stx := Syntax.List $ p.map (λ o, o.cmd),
   let stx := stx.updateLeading s,
   some s' ← pure $ stx.reprint | IO.println "reprint fail: choice Node",
   when (s ≠ s') (
     IO.println "reprint fail:" *>
     IO.println s'
   )

def showResult (p : List moduleParserOutput) (s : String) : ExceptT String IO Unit :=
let stx := Syntax.List $ p.map (λ r, r.cmd) in
let stx := stx.updateLeading s in
let msgs := (do r ← p, r.messages.toList) in
match msgs with
| [] := do
  IO.println "Result:",
  IO.println (toString stx)
| msgs := do
  msgs.mfor $ λ e, IO.println e.toString,
  IO.println "partial Syntax tree:",
  IO.println (toString stx)

def parseModule (s : String) : Except String (List moduleParserOutput) :=
do cfg ← mkConfig,
   (outputs, Sum.inl (), ⟨[]⟩) ← pure $ coroutine.finish (λ_, cfg)
     (Parser.run cfg s (λ st _, Module.Parser.run st)) cfg
     | Except.error "final Parser output should be Empty!",
   pure outputs

def showParse (s : String) : ExceptT String IO Unit :=
do r ← MonadExcept.liftExcept $ parseModule s,
   checkReprint r s,
   showResult r s

#eval showParse "prelude"
#eval showParse "import me"
#eval showParse "importme"
#eval showParse "import"

#eval showParse "prelude
import ..a b
import c"

#eval showParse "open me you"
#eval showParse "open me as you (a b c) (renaming a->b c->d) (hiding a b)"
#eval showParse "open me you."
#eval showParse "open open"
#eval showParse "open me import open you"

#eval showParse "open a
section b
  open c
  section d
    open e
  end d
end b"

-- should not be a Parser error
#eval showParse "section a end"

universes u v
#check Type max u v  -- eh
-- parsed as `Type (max) (u) (v)`, will fail on elaboration ("max: must have at least two arguments", "Function expected at 'Type'", "unknown identifier 'u'/'v'")
#eval showParse "#check Type max u v"

#eval do
  [header, nota, eoi] ← parseModule "infixl `+`:65 := Nat.add" | throw "huh",
  Except.ok cmd' ← pure $ (expand nota.cmd).run {filename := "foo", input := "", transformers := builtinTransformers} | throw "heh",
  pure cmd'.reprint

-- test overloading
#eval do
  let s := "
prelude
constant α : Type
constant a : α
namespace foo
  constant α : Type
end foo
constant b : α
open foo
constant c : α",
  runFrontend s (IO.println ∘ Message.toString),
  pure ()

-- "sticky" `open`
#eval do
  let s := "
prelude
open foo
constant foo.α : Type
constant b : α",
  runFrontend s (IO.println ∘ Message.toString),
  pure ()

#exit

-- slowly progressing...
setOption profiler True
#eval do
  s ← IO.Fs.readFile "../../library/init/core.Lean",
  --let s := (s.mkIterator.nextn 10000).prevToString,
  runFrontend "core.Lean" s (IO.println ∘ Message.toString),
  pure ()
