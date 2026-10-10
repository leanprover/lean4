/-!
This test is a regression test for constant folding of uint literals.
-/

/--
trace: [Compiler.result] size: 1
    def mwe : UInt8 :=
      let _x.1 : UInt8 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def mwe : Bool :=
    let x8 := 1
    let y8 := 2
    let x16 := 1
    let y16 := 2
    let x32 := 1
    let y32 := 2
    let x64 := 1
    let y64 := 2
    x8 + y8 < 4 && x16 + y16 < 4 && x32 + y32 < 4 && x64 + y64 < 4
