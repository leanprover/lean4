-- Type has trivial structure, so `u64` representation is expected.
structure Unboxed where val : UInt64

structure S where
  unboxed : Unboxed
  unused : Bool

/--
trace: [Compiler.IR] [result]
    def get_unboxed (x_1 : obj) : u64 :=
      let x_2 : obj := proj[0] x_1;
      inc x_2;
      dec x_1;
      let x_3 : u64 := unbox x_2;
      dec x_2;
      ret x_3
    def get_unboxed._boxed (x_1 : obj) : obj :=
      let x_2 : u64 := get_unboxed x_1;
      let x_3 : obj := box x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
@[export get_unboxed]
def get_unboxed (s : S) : UInt64 := s.unboxed.val

