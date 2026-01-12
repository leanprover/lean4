/-!
This test is a regression test for constant folding of uint literals.
-/

/--
trace: [Compiler.IR] [result]
    def mwe : u8 :=
      let x_1 : u8 := 1;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
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

