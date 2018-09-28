import init.lean.parser.module init.lean.expander init.lean.elaborator init.io
open lean
open lean.parser
open lean.expander
open lean.elaborator

def check_reprint (p : list module_parser_output) (s : string) : except_t string io unit :=
let stx := syntax.node ⟨none, p.map (λ o, o.cmd)⟩ in
let stx := stx.update_leading s in
when (stx.reprint ≠ s) (
  io.println "reprint fail:" *>
  io.println stx.reprint
)

def show_result (p : list module_parser_output) (s : string) : except_t string io unit :=
let stx := syntax.node ⟨none, p.map (λ r, r.cmd)⟩ in
let stx := stx.update_leading s in
let msgs := (do r ← p, r.messages.to_list) in
match msgs with
| [] := do
  io.println "result:",
  io.println (to_string stx)
| msgs := do
  msgs.mfor $ λ e, io.println e.text,
  io.println "partial syntax tree:",
  io.println (to_string stx)

def mk_config : except string module_parser_config :=
do t ← parser.mk_token_trie $
    parser.tokens module.parser ++
    parser.tokens command.builtin_command_parsers ++
    parser.tokens term.builtin_leading_parsers ++
    parser.tokens term.builtin_trailing_parsers,
   pure $ {
     filename := "<unknown>", tokens := t,
     command_parsers := command.builtin_command_parsers,
     leading_term_parsers := term.builtin_leading_parsers,
     trailing_term_parsers := term.builtin_trailing_parsers,
   }

def parse_module (s : string) : except string (list module_parser_output) :=
do cfg ← mk_config,
   (outputs, sum.inl (), ⟨[]⟩) ← pure $ coroutine.finish (λ_, cfg)
     (parser.run cfg s (λ _, module.parser)) cfg
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
  except.ok cmd' ← pure $ (expand nota.cmd).run {filename := "init/core.lean"} | throw "heh",
  pure cmd'.reprint

-- slowly progressing...
#eval (do {
  s ← io.fs.read_file "../../library/init/core.lean",
  let s := (s.mk_iterator.nextn 7000).prev_to_string,
  parser_cfg ← monad_except.lift_except $ mk_config,
  let cfg : elaborator_config := {filename := "foo"},
  let st : elaborator_state := {parser_cfg := {..parser_cfg}},
  let k := parser.run parser_cfg s (λ _, module.parser),
  outs ← io.prim.iterate_eio (k, st, ([] : list module_parser_output)) $ λ ⟨k, st, outs⟩, match k.resume st.parser_cfg with
    | coroutine_result_core.done p := pure (sum.inr outs.reverse)
    | coroutine_result_core.yielded out k := do {
      match out.messages.to_list with
      | [] := pure () /-do
        io.println "result:",
        io.println (to_string stx)-/
      | msgs := do {
        msgs.mfor $ λ e, io.println e.text/-,
        io.println "partial syntax tree:",
        io.println (to_string out.cmd)-/
      },
      --io.println out.cmd,
      match (expand out.cmd).run {filename := "init/core.lean"} with
      | except.ok cmd' := do {
        --io.println cmd',
        match ((elaborate cmd').run cfg).run st with
        | except.ok ((), st) := pure (sum.inl (k, st, out :: outs))
        | except.error e := throw e.text
      }
      | except.error e := throw e.text
    },
  check_reprint outs s,
  let stx := syntax.node ⟨none, outs.map (λ r, r.cmd)⟩,
  let stx := stx.update_leading s,
  io.println "result:",
  io.println (to_string stx)
} : except_t string io unit)
