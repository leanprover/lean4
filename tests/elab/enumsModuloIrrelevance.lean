inductive E1 (n : Nat) where
  | a
  | b
  | c

/--
trace: [Compiler.IR] [result]
    def e1 : u8 :=
      let x_1 : u8 := 2;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def e1 : E1 7 := .c

inductive E2 where
  | a (p : 0 = 0)
  | b (p : 1 = 1)
  | c (p : 0 = 1)

/--
trace: [Compiler.IR] [result]
    def e2 : u8 :=
      let x_1 : u8 := 1;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def e2 : E2 := .b rfl

inductive E3 (m n : Nat) where
  | a (p : 0 = 0)
  | b (p : 1 = 1)
  | c (p : 0 = 0) (q : 1 = 1)

/--
trace: [Compiler.IR] [result]
    def e3 : u8 :=
      let x_1 : u8 := 2;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def e3 : E3 7 11 := .c rfl rfl
