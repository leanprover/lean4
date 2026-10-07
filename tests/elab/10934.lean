set_option trace.Compiler.result true
set_option pp.letVarTypes true
set_option pp.funBinderTypes true

/--
trace: [Compiler.result] size: 7
    def _example (a : UInt8) (b : UInt8) : UInt8 :=
      cases b : UInt8
      | Bool.false =>
        cases a : UInt8
        | Bool.false =>
          let _x.1 : UInt8 := 1;
          return _x.1
        | Bool.true =>
          return b
      | Bool.true =>
        return a
[Compiler.result] size: 4
    def _example._boxed (a : tagged) (b : tagged) : tagged :=
      let a.boxed : UInt8 := unbox a;
      let b.boxed : UInt8 := unbox b;
      let res : UInt8 := _example a.boxed b.boxed;
      let r : tagged := box res;
      return r
-/
#guard_msgs in
example (a b : Bool) : Bool := decide (a ↔ b)

/--
trace: [Compiler.result] size: 4
    def _example (a : UInt8) (b : UInt8) : UInt8 :=
      cases a : UInt8
      | Bool.false =>
        let _x.1 : UInt8 := 1;
        return _x.1
      | Bool.true =>
        return b
[Compiler.result] size: 4
    def _example._boxed (a : tagged) (b : tagged) : tagged :=
      let a.boxed : UInt8 := unbox a;
      let b.boxed : UInt8 := unbox b;
      let res : UInt8 := _example a.boxed b.boxed;
      let r : tagged := box res;
      return r
-/
#guard_msgs in
example (a b : Bool) : Bool := decide (a → b)

/--
trace: [Compiler.result] size: 3
    def _example (a : UInt8) (b : UInt8) : UInt8 :=
      cases a : UInt8
      | Bool.false =>
        return a
      | Bool.true =>
        return b
[Compiler.result] size: 4
    def _example._boxed (a : tagged) (b : tagged) : tagged :=
      let a.boxed : UInt8 := unbox a;
      let b.boxed : UInt8 := unbox b;
      let res : UInt8 := _example a.boxed b.boxed;
      let r : tagged := box res;
      return r
-/
#guard_msgs in
example (a b : Bool) : Bool := decide (∃ _ : a, b)

/--
trace: [Compiler.result] size: 0
    def _example (a : UInt8) : UInt8 :=
      return a
[Compiler.result] size: 3
    def _example._boxed (a : tagged) : tagged :=
      let a.boxed : UInt8 := unbox a;
      let res : UInt8 := _example a.boxed;
      let r : tagged := box res;
      return r
-/
#guard_msgs in
example (a : Bool) : Bool := decide (if _h : a then True else False)
