-- Type has trivial structure, so `u64` representation is expected.
structure Unboxed where val : UInt64

structure S where
  unboxed : Unboxed
  unused : Bool

/--
trace: [Compiler.IR] [result]
    def get_unboxed (x_1 : obj) : u64 :=
      let x_2 : u64 := sproj[0, 0] x_1;
      dec x_1;
      ret x_2
    def get_unboxed._boxed (x_1 : obj) : tobj :=
      let x_2 : u64 := get_unboxed x_1;
      let x_3 : tobj := box x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
@[export get_unboxed]
def get_unboxed (s : S) : UInt64 := s.unboxed.val
