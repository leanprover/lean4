import system.io
import init.lean.ir.parser init.lean.ir.format
import init.lean.ir.elim_phi

open lean.parser
open lean.ir

def show_result {α} [lean.has_to_format α] (p : parser α) (s : string) : io unit :=
match parse p s with
| except.ok a    := io.print_ln (lean.to_fmt a)
| except.error e := io.print_ln (e.to_string s)

def IR1 := "
def succ (x : uint32) : uint32 :=
main: one : uint32 := 1; x1 : uint32 := add x one; ret x1;
"

#eval show_result (whitespace >> parse_def) IR1

def IR2 := "
def add_n (x : uint32) (y : uint32) (n : uint32) : uint32 :=
main: jmp loop;
loop:
  r1   : uint32 := phi x r2;
  y1   : uint32 := phi y y1;
  n1   : uint32 := phi n n2;
  r2   : uint32 := add r1 y1;
  one  : uint32 := 1;
  n2   : uint32 := sub n1 one;
  zero : uint32 := 0;
  c    : bool   := eq n2 zero;
  case c loop end;
end:
  r3   : uint32 := phi r2;
  ret r3;
"

#eval show_result (whitespace >> parse_def) IR2

def tst_elim_phi (s : string) : io unit :=
do (except.ok ir) ← return $ parse (whitespace >> parse_def) s,
   io.print_ln (lean.to_fmt (elim_phi ir))

#eval tst_elim_phi IR2
