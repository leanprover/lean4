/-!
This test is a regression for issue #10443 where the RC analysis would wrongfully insert ref counts
for large `UInt64` constants.
-/


def gSize : UInt64 := 0x8000000000000000

/--
trace: [Compiler.result] size: 2
    def mwe (y : UInt64) : UInt64 :=
      let x : UInt64 := 9223372036854775808;
      let _x.1 : UInt64 := UInt64.add x y;
      return _x.1
[Compiler.result] size: 4
    def mwe._boxed (y : obj) : obj :=
      let y.boxed : UInt64 := unbox y;
      dec[ref] y;
      let res : UInt64 := mwe y.boxed;
      let r : obj := box res;
      return r
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def mwe (y : UInt64) : UInt64 :=
    let x := gSize
    let y := y
    x + y
