import system.io
import init.lean.ir.parser init.lean.ir.format
import init.lean.ir.elim_phi init.lean.ir.type_check
import init.lean.ir.extract_cpp

open lean.parser
open lean.parser.monad_parser
open lean.ir

def check_decl (d : decl) : io unit :=
match type_check d with
| except.ok _    := return ()
| except.error e := io.print_ln (to_string e)

def show_result (p : parser decl) (s : string) : io unit :=
match parser_t.parse p s with
| except.ok d    := io.print_ln (lean.to_fmt d) >> check_decl d
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
  case c [loop, end];
end:
  r3   : uint32 := phi r2;
  ret r3;
"

#eval show_result (whitespace >> parse_def) IR2

def tst_elim_phi (s : string) : io unit :=
do (except.ok d) ← return $ parser_t.parse (whitespace >> parse_def) s,
   check_decl d,
   io.print_ln (lean.to_fmt (elim_phi d))

#eval tst_elim_phi IR2

def IR3 := "
def mk_struct (d1 : object) (d2 : uint32) (d3 : usize) (d4 : uint32) (d5 : bool) (d6 : bool) : object :=
main:
  o := cnstr 0 1 18;
  set o 0 d1;
  sset o 8 d3;
  sset o 16 d2;
  sset o 20 d4;
  sset o 24 d5;
  sset o 25 d6;
  ret o;
"
#eval show_result (whitespace >> parse_def) IR3

def tst_extract_cpp (s : string) : io unit :=
do (except.ok d) ← return $ parser_t.parse (whitespace >> parse_def) s,
   check_decl d,
   match extract_cpp [elim_phi d] with
   | except.ok code := io.print_ln code
   | except.error s := io.print_ln s

#eval tst_extract_cpp IR3
#eval tst_extract_cpp IR2

def IR4 := "
def swap (d1 : object) (d2 : object) : object object :=
main:
  r1 := cnstr 0 2 0;
  r2 := cnstr 0 2 0;
  set r1 0 d1;
  set r1 1 d2;
  inc d1;
  inc d2;
  set r2 0 d2;
  set r2 1 d1;
  ret r1 r2;
"

#eval tst_extract_cpp IR4
