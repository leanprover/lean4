import system.io
import init.lean.ir.parser init.lean.ir.format

open lean.parser
open lean.ir

def show_result {α} [lean.has_to_format α] (p : parser α) (s : string) : io unit :=
match parse p s with
| except.ok a    := io.print_ln (lean.to_fmt a)
| except.error e := io.print_ln (e.to_string s)
end

def IR := "
def succ (x : uint32) : uint32 :=
main: one : uint32 := 1; x1 : uint32 := add x one; ret x1;
"

#eval show_result (whitespace >> parse_def) IR
