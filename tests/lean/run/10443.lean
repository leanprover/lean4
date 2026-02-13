/-!
This test is a regression for issue #10443 where the RC analysis would wrongfully insert ref counts
for large `UInt64` constants.
-/


def gSize : UInt64 := 0x8000000000000000

/--
trace: [Compiler.IR] [result]
    def mwe (x_1 : u64) : u64 :=
      let x_2 : u64 := 9223372036854775808;
      let x_3 : u64 := UInt64.add x_2 x_1;
      ret x_3
    def mwe._boxed (x_1 : obj) : obj :=
      let x_2 : u64 := unbox x_1;
      dec x_1;
      let x_3 : u64 := mwe x_2;
      let x_4 : obj := box x_3;
      ret x_4
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def mwe (y : UInt64) : UInt64 :=
    let x := gSize
    let y := y
    x + y

