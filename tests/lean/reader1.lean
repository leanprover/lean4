import init.lean.parser.reader.module init.io
open lean.parser
open lean.parser.reader

def show_result (p : lean.parser.reader) (s : string) : eio unit :=
let (stx, errors) := p.parse ⟨⟩ s in
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

#eval show_result module.reader "prelude"
#eval show_result module.reader "import me"
#eval show_result module.reader "importme"
#eval show_result module.reader "import"

#eval show_result module.reader "prelude
import ..a b
import c"

#eval show_result module.reader "open me you"
#eval show_result module.reader "open me as you (a b c) (renaming a->b c->d) (hiding a b)"
#eval show_result module.reader "open me you."
#eval show_result module.reader "open open"
#eval show_result module.reader "open me import open you"

#eval show_result module.reader "open a
section b
  open c
  section d
    open e
  end d
end b"

-- should not be a reader error
#eval show_result module.reader "section a end"

#eval show_result module.reader "notation `Prop` := _"

#eval show_result mixfix.reader "prefix `+`:10 := _"
#eval (do {
  let (stx, _) := mixfix.reader.parse ⟨⟩ "prefix `+`:10 := _",
  some {root := stx, ..} ← pure $ reader.parse.view stx,
  some stx ← pure $ mixfix.expand stx | throw "expand fail",
  io.println stx,
  io.println stx.reprint
} : except_t string io unit)

-- slowly progressing...
#eval do
  s ← io.fs.read_file "../../library/init/core.lean",
  show_result module.reader $ (s.mk_iterator.nextn 1700).prev_to_string
