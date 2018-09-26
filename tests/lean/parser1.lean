import init.lean.parser.module init.lean.expander init.io
open lean
open lean.parser
open lean.expander

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

def parse_module (s : string) : except string (list module_parser_output) :=
do st ← parser.mk_parser_state (parser.tokens module.parser),
   (outputs, sum.inl (), ⟨[]⟩) ← pure $ coroutine.finish (λ cmd, ()) (parser.run ⟨"<unknown>"⟩ st s module.parser) ()
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

-- slowly progressing...
#eval (do {
  s ← io.fs.read_file "../../library/init/core.lean",
  let s := (s.mk_iterator.nextn 6500).prev_to_string,
  st ← monad_except.lift_except $ parser.mk_parser_state (tokens module.parser),
  let k := parser.run ⟨"init/core.lean"⟩ st s module.parser,
  outs ← io.prim.iterate_eio (k, ([] : list module_parser_output)) $ λ ⟨k, outs⟩, match k.resume () with
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
      match (expand out.cmd).run {filename := "init/core.lean"} with
      | except.ok cmd' := pure (sum.inl (k, out :: outs))
      | except.error e := throw e.text
    },
  check_reprint outs s,
  let stx := syntax.node ⟨none, outs.map (λ r, r.cmd)⟩,
  let stx := stx.update_leading s,
  io.println "result:",
  io.println (to_string stx)
} : except_t string io unit)
