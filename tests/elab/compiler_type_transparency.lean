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
trace: [Compiler.result] size: 1
    def A.foo (_y.1 : @&tobj) : tobj :=
      inc _y.1;
      return _y.1
[Compiler.result] size: 2
    def A.foo._boxed (_y.1 : tobj) : tobj :=
      let res : tobj := A.foo _y.1;
      dec _y.1;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def foo : Function Nat Nat := Function.id

end A

namespace B

def Function (α β : Type) := α → β

namespace Function

@[inline]
def id : Function α α := fun x => x

end Function

/--
trace: [Compiler.result] size: 1
    def B.foo (a.1 : @&tobj) : tobj :=
      inc a.1;
      return a.1
[Compiler.result] size: 2
    def B.foo._boxed (a.1 : tobj) : tobj :=
      let res : tobj := B.foo a.1;
      dec a.1;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def foo : Function Nat Nat := Function.id

end B
