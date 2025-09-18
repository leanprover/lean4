/-!
This test is a regression for issue #10443 where the RC analysis would wrongfully insert ref counts
for large `UInt64` constants.
-/


def gSize : UInt64 := 0x8000000000000000

/--
trace: [Compiler.IR] [result]
    def mwe._closed_0 : u64 :=
      let x_1 : u64 := 9223372036854775808;
      let x_2 : u64 := UInt64.add x_1 x_1;
      ret x_2
    def mwe : u64 :=
      let x_1 : u64 := mwe._closed_0;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def mwe : UInt64 :=
    let x := gSize
    let y := gSize
    x + y

