module

/-!
This test asserts that disabling user-defined borrow annotations works. This is sometimes required for
export/extern pairs
-/

public abbrev Foo (α : Type) := (x : @& α) → α

/--
trace: [Compiler.result] size: 0
    def t1 @&x : tobj :=
      extern
[Compiler.result] size: 2
    def t1._boxed x : tobj :=
      let res := t1 x;
      dec x;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
@[extern "t1"]
public opaque t1 : Foo Nat

/--
trace: [Compiler.result] size: 0
    def t2 x : tobj :=
      extern
[Compiler.result] size: 1
    def t2._boxed x : tobj :=
      let res := t2 x;
      return res
-/
#guard_msgs in
set_option compiler.ignoreBorrowAnnotation true in
set_option trace.Compiler.result true in
@[extern "t2"]
public opaque t2 : Foo Nat
