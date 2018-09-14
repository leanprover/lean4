import init.lean.parser.module init.io
open lean
open lean.parser
open lean.parser.syntax_node_kind.has_view

def show_result (p : syntax × message_log) (s : string) : eio unit :=
let (stx, msgs) := p in
/-when (stx.reprint ≠ s) (
  io.println "reprint fail:" *>
  io.println stx.reprint
) *>-/
match msgs.to_list with
| [] := do
  io.println "result: ",
  io.println (to_string stx)
| msgs := do
  msgs.mfor $ λ e, io.println e.text,
  io.println "partial syntax tree:",
  io.println (to_string stx)

def parse_module (s : string) : syntax × message_log :=
coroutine.finish (λ cmd, ()) (parser.parse ⟨"<unknown>"⟩ s module.parser) ()

def show_parse (s : string) : eio unit :=
show_result (parse_module s) s

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

-- expansion example
#eval (do {
  (stx, ⟨[]⟩) ← pure $ parse_module "prefix `+`:10 := _",
  some {root := stx, ..} ← pure $ parser.parse.view stx,
  some {commands := [stx], ..} ← pure $ view module stx,
  some stx ← pure $ mixfix.expand stx | throw "expand fail",
  io.println stx,
  io.println stx.reprint
} : except_t string io unit)

-- slowly progressing...
#eval do
  s ← io.fs.read_file "../../library/init/core.lean",
  let s := (s.mk_iterator.nextn 1700).prev_to_string,
  let k := parser.parse ⟨"foo"⟩ s module.parser,
  io.prim.iterate_eio k $ λ k, match k.resume () with
    | coroutine_result_core.done p := show_result p s *> pure (sum.inr ())
    | coroutine_result_core.yielded cmd k := do {
      --io.println "command:" *> io.println cmd,
      pure (sum.inl k)
    }
