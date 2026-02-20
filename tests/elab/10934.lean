set_option trace.compiler.ir.result true

/--
trace: [Compiler.IR] [result]
    def _example (x_1 : u8) (x_2 : u8) : u8 :=
      case x_1 : u8 of
      Bool.false →
        case x_2 : u8 of
        Bool.false →
          let x_3 : u8 := 1;
          ret x_3
        Bool.true →
          ret x_1
      Bool.true →
        ret x_2
    def _example._boxed (x_1 : tagged) (x_2 : tagged) : tagged :=
      let x_3 : u8 := unbox x_1;
      let x_4 : u8 := unbox x_2;
      let x_5 : u8 := _example x_3 x_4;
      let x_6 : tagged := box x_5;
      ret x_6
-/
#guard_msgs in
example (a b : Bool) : Bool := decide (a ↔ b)

/--
trace: [Compiler.IR] [result]
    def _example (x_1 : u8) (x_2 : u8) : u8 :=
      case x_1 : u8 of
      Bool.false →
        let x_3 : u8 := 1;
        ret x_3
      Bool.true →
        ret x_2
    def _example._boxed (x_1 : tagged) (x_2 : tagged) : tagged :=
      let x_3 : u8 := unbox x_1;
      let x_4 : u8 := unbox x_2;
      let x_5 : u8 := _example x_3 x_4;
      let x_6 : tagged := box x_5;
      ret x_6
-/
#guard_msgs in
example (a b : Bool) : Bool := decide (a → b)

/--
trace: [Compiler.IR] [result]
    def _example (x_1 : u8) (x_2 : u8) : u8 :=
      case x_1 : u8 of
      Bool.false →
        ret x_1
      Bool.true →
        ret x_2
    def _example._boxed (x_1 : tagged) (x_2 : tagged) : tagged :=
      let x_3 : u8 := unbox x_1;
      let x_4 : u8 := unbox x_2;
      let x_5 : u8 := _example x_3 x_4;
      let x_6 : tagged := box x_5;
      ret x_6
-/
#guard_msgs in
example (a b : Bool) : Bool := decide (∃ _ : a, b)

/--
trace: [Compiler.IR] [result]
    def _example (x_1 : u8) : u8 :=
      ret x_1
    def _example._boxed (x_1 : tagged) : tagged :=
      let x_2 : u8 := unbox x_1;
      let x_3 : u8 := _example x_2;
      let x_4 : tagged := box x_3;
      ret x_4
-/
#guard_msgs in
example (a : Bool) : Bool := decide (if _h : a then True else False)
