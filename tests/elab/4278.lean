-- Type has trivial structure, so `u64` representation is expected.
structure Unboxed where val : UInt64

structure S where
  unboxed : Unboxed
  unused : Bool

/--
trace: [Compiler.result] size: 2
    def get_unboxed (s : obj) : UInt64 :=
      let unboxed : UInt64 := sproj[0, 0] s;
      dec[ref] s;
      return unboxed
[Compiler.result] size: 2
    def get_unboxed._boxed (s : obj) : obj :=
      let res : UInt64 := get_unboxed s;
      let r : obj := box res;
      return r
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
@[export get_unboxed]
def get_unboxed (s : S) : UInt64 := s.unboxed.val
