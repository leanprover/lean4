/-!
This test ensures that the code generator sees the same type representation regardless of
transparency setting in the elaborator. If this test ever breaks you should ensure that the IR
between A and B is in sync.
-/

namespace A

@[irreducible] def Function (α β : Type) := α → β

namespace Function

attribute [local semireducible] Function

@[inline]
def id : Function α α := fun x => x

end Function

/--
trace: [Compiler.IR] [result]
    def A.foo (x_1 : @& tobj) : tobj :=
      inc x_1;
      ret x_1
    def A.foo._boxed (x_1 : tobj) : tobj :=
      let x_2 : tobj := A.foo x_1;
      dec x_1;
      ret x_2
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def foo : Function Nat Nat := Function.id

end A

namespace B

def Function (α β : Type) := α → β

namespace Function

@[inline]
def id : Function α α := fun x => x

end Function

/--
trace: [Compiler.IR] [result]
    def B.foo (x_1 : @& tobj) : tobj :=
      inc x_1;
      ret x_1
    def B.foo._boxed (x_1 : tobj) : tobj :=
      let x_2 : tobj := B.foo x_1;
      dec x_1;
      ret x_2
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def foo : Function Nat Nat := Function.id

end B
