import init.lean.frontend init.io
open lean
open lean.parser
open lean.expander
open lean.elaborator

def check_reprint (p : list module_parser_output) (s : string) : except_t string io unit :=
do let stx := syntax.list $ p.map (λ o, o.cmd),
   let stx := stx.update_leading s,
   some s' ← pure $ stx.reprint | io.println "reprint fail: choice node",
   when (s ≠ s') (
     io.println "reprint fail:" *>
     io.println s'
   )

def show_result (p : list module_parser_output) (s : string) : except_t string io unit :=
let stx := syntax.list $ p.map (λ r, r.cmd) in
let stx := stx.update_leading s in
let msgs := (do r ← p, r.messages.to_list) in
match msgs with
| [] := do
  io.println "result:",
  io.println (to_string stx)
| msgs := do
  msgs.mfor $ λ e, io.println e.to_string,
  io.println "partial syntax tree:",
  io.println (to_string stx)

def parse_module (s : string) : except string (list module_parser_output) :=
do cfg ← mk_config,
   (outputs, sum.inl (), ⟨[]⟩) ← pure $ coroutine.finish (λ_, cfg)
     (parser.run cfg s (λ st _, module.parser.run st)) cfg
     | except.error "final parser output should be empty!",
   pure outputs

def show_parse (s : string) : except_t string io unit :=
do r ← monad_except.lift_except $ parse_module s,
   check_reprint r s,
   show_result r s

#eval show_parse "prelude"
#eval show_parse "import me"
#eval show_parse "importme"
#eval show_parse "import"

#eval show_parse "prelude
import ..a b
import c"

#eval show_parse "open me you"
#eval show_parse "open me as you (a b c) (renaming a->b c->d) (hiding a b)"
#eval show_parse "open me you."
#eval show_parse "open open"
#eval show_parse "open me import open you"

#eval show_parse "open a
section b
  open c
  section d
    open e
  end d
end b"

-- should not be a parser error
#eval show_parse "section a end"

universes u v
#check Type max u v  -- eh
-- parsed as `Type (max) (u) (v)`, will fail on elaboration ("max: must have at least two arguments", "function expected at 'Type'", "unknown identifier 'u'/'v'")
#eval show_parse "#check Type max u v"

#eval do
  [header, nota, eoi] ← parse_module "infixl `+`:65 := nat.add" | throw "huh",
  except.ok cmd' ← pure $ (expand nota.cmd).run {filename := "foo", input := "", transformers := builtin_transformers} | throw "heh",
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
  run_frontend s (io.println ∘ message.to_string),
  pure ()

-- "sticky" `open`
#eval do
  let s := "
prelude
open foo
constant foo.α : Type
constant b : α",
  run_frontend s (io.println ∘ message.to_string),
  pure ()

#exit

-- slowly progressing...
set_option profiler true
#eval do
  s ← io.fs.read_file "../../library/init/core.lean",
  --let s := (s.mk_iterator.nextn 10000).prev_to_string,
  run_frontend "core.lean" s (io.println ∘ message.to_string),
  pure ()
