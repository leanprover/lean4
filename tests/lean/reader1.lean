import init.lean.parser.reader system.io
open lean.parser

def show_result (p : lean.parser.reader syntax) (s : string) : io unit :=
match p.parse ⟨⟩ ⟨ff, []⟩ s with
| except.ok a    := io.print_ln "result: " >> io.print_ln (to_string a)
| except.error e := io.print_ln (e.to_string s)

#eval show_result module.reader "prelude"
#eval show_result module.reader "import me"
#eval show_result module.reader "noncomputable theory"

-- wrong: "noncomputable" recognized as identifier
#eval show_result module.reader "prelude
import ..a b
noncomputable theory"
