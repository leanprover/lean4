set_option trace.Compiler.saveBase true in
def f1 (c : Bool) (a b : Nat) :=
  let k d y z :=
    match d with
    | true => y + z + z*y
    | false => z + y
  match c with
  | true => k false a b
  | false => k true b a

set_option trace.Compiler.saveBase true in
def f2 (c : Bool) (a b : Nat) :=
  let k y d z :=
    match d with
    | true => y + z + z*y
    | false => z + y
  match c with
  | true => k a false b
  | false => k b true a

inductive C where
  | c1 | c2 | c3 | c4

set_option trace.Compiler.saveBase true in
def f3 (c c' : C) (a b : Nat) :=
  let k y (d : C) z :=
    match d with
    | C.c1 => y + z + z*y
    | _ => z + y + y
  match c with
  | .c1 => k a .c2 b
  | .c2 => k b .c1 a
  | .c3 => k b c' a
  | .c4 => k a c' a

set_option trace.Compiler.saveBase true in
def f4 (c c' : C) (a b : Nat) :=
  let k y z (d : C) :=
    match d with
    | C.c1 => y + z + z*y
    | C.c3 => y*y+a
    | _ => z + y + y
  match c with
  | .c1 => k a b .c2
  | .c2 => k b b .c1
  | .c3 => k b a c'
  | .c4 => k a a c'
