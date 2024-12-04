set_option trace.Compiler.saveBase true in
def f1 (c : Bool) (a b : Nat) :=
  let k d y z :=
    match d with
    | true => y + z + z*y
    | false => z + y
  match c with
  | true => k true a b
  | false => k false b a

set_option trace.Compiler.saveBase true in
def f2 (c : Bool) (a b : Nat) :=
  let k d y z :=
    match d with
    | true => y + z + z*y
    | false => z + y
  match c with
  | true => k c a b
  | false => k c b a

inductive C where
  | c1 | c2 | c3 | c4

set_option trace.Compiler.saveBase true in
def f3 (c c' : C) (a b : Nat) :=
  let k y z (d : C) :=
    match d with
    | C.c1 => y + z + z*y
    | C.c3 => y*y+a
    | _ => z + y + y
  match c with
  | .c1 => k a b c
  | .c2 => k b b c
  | .c3 => k b a c'
  | .c4 => k a a c'
