inductive E1 (n : Nat) where
  | a
  | b
  | c

/--
trace: [Compiler.result] size: 1
    def e1 : UInt8 :=
      let _x.1 : UInt8 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def e1 : E1 7 := .c

inductive E2 where
  | a (p : 0 = 0)
  | b (p : 1 = 1)
  | c (p : 0 = 1)

/--
trace: [Compiler.result] size: 1
    def e2 : UInt8 :=
      let _x.1 : UInt8 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def e2 : E2 := .b rfl

inductive E3 (m n : Nat) where
  | a (p : 0 = 0)
  | b (p : 1 = 1)
  | c (p : 0 = 0) (q : 1 = 1)

/--
trace: [Compiler.result] size: 1
    def e3 : UInt8 :=
      let _x.1 : UInt8 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def e3 : E3 7 11 := .c rfl rfl
