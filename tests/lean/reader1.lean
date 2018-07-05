import init.lean.parser.reader.module system.io
open lean.parser
open lean.parser.reader

def show_result (p : lean.parser.reader syntax) (s : string) : io unit :=
match p.parse ⟨⟩ ⟨[
  ⟨"prelude", none⟩,
  ⟨"import", none⟩,
  ⟨"noncomputable", none⟩,
  ⟨"theory", none⟩,
  ⟨"/-", none⟩,
  ⟨"--", none⟩
], ff, []⟩ s with
| except.ok a    := io.print_ln "result: " >> io.print_ln (to_string a)
| except.error e := io.print_ln (e.to_string s)

#eval show_result module.reader "prelude"
#eval show_result module.reader "import me"
#eval show_result module.reader "noncomputable theory"

#eval show_result module.reader "prelude
import ..a b
noncomputable theory"
