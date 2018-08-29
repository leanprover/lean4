import init.lean.parser.reader.module init.io
open lean.parser
open lean.parser.reader

def show_result (p : syntax × list lean.message) (s : string) : eio unit :=
let (stx, errors) := p in
when (stx.reprint ≠ s) (
  io.println "reprint fail:" *>
  io.println stx.reprint
) *>
match errors with
| [] := do
  io.println "result: ",
  io.println (to_string stx)
| _ := do
  errors.mfor $ λ e, io.println e,
  io.println "partial syntax tree:",
  io.println (to_string stx)

def show_parse (p : module_reader) [has_tokens p] (s : string) : eio unit :=
show_result (coroutine.finish (λ cmd, ()) (reader.parse ⟨⟩ s p) ()) s

#eval show_parse module.reader "prelude"
#eval show_parse module.reader "import me"
#eval show_parse module.reader "importme"
#eval show_parse module.reader "import"

#eval show_parse module.reader "prelude
import ..a b
import c"

#eval show_parse module.reader "open me you"
#eval show_parse module.reader "open me as you (a b c) (renaming a->b c->d) (hiding a b)"
#eval show_parse module.reader "open me you."
#eval show_parse module.reader "open open"
#eval show_parse module.reader "open me import open you"

#eval show_parse module.reader "open a
section b
  open c
  section d
    open e
  end d
end b"

-- should not be a reader error
#eval show_parse module.reader "section a end"

#eval show_parse module.reader "notation `Prop` := _"

-- expansion example
#eval (do {
  let (stx, _) := reader.parse ⟨⟩ "prefix `+`:10 := _" $ combinators.with_recurse mixfix.reader,
  some {root := stx, ..} ← pure $ reader.parse.view stx,
  some stx ← pure $ mixfix.expand stx | throw "expand fail",
  io.println stx,
  io.println stx.reprint
} : except_t string io unit)

-- slowly progressing...
#eval do
  s ← io.fs.read_file "../../library/init/core.lean",
  let s := (s.mk_iterator.nextn 1700).prev_to_string,
  let k := reader.parse ⟨⟩ s module.reader,
  io.prim.iterate_eio k $ λ k, match k.resume () with
    | coroutine_result_core.done p := show_result p s *> pure (sum.inr ())
    | coroutine_result_core.yielded cmd k := do {
      --io.println "command:" *> io.println cmd,
      pure (sum.inl k)
    }
