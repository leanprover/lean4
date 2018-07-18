import init.lean.parser.reader.module system.io
open lean.parser
open lean.parser.reader

def show_result (p : lean.parser.reader) (s : string) : io unit :=
match p.parse ⟨⟩ s with
| except.ok stx  := do
  guard $ stx.reprint = s,
  io.print_ln "result: ",
  io.print_ln (to_string stx)
| except.error e := io.print_ln (e.to_string s)

#eval show_result module.reader "prelude"
#eval show_result module.reader "import me"
#eval show_result module.reader "importme"

#eval show_result module.reader "prelude
import ..a b
import c"

#eval show_result module.reader "open me you"
#eval show_result module.reader "open me as you (a b c) (renaming a->b c->d) (hiding a b)"

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

-- slowly progressing...
#eval do
  s ← io.fs.read_file "../../library/init/core.lean",
  show_result module.reader s
