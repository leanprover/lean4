#eval (Thunk.pure 1).get
#eval (Thunk.mk fun _ => 2).get
#eval
  let t1 := Thunk.mk fun _ => dbg_trace 4; 5
  let t2 := Thunk.mk fun _ => dbg_trace 3; 0
  let v2 := t2.get
  let v1 := t1.get
  v1 + v2
#eval
  let t1 := Thunk.pure 8 |>.map fun n => dbg_trace 7; n
  let t2 := Thunk.mk fun _ => dbg_trace 6; 0
  let v2 := t2.get
  let v1 := t1.get
  v1 + v2
#eval
  let t1 := Thunk.pure 11 |>.bind fun n => dbg_trace 10; Thunk.pure n
  let t2 := Thunk.mk fun _ => dbg_trace 9; 0
  let v2 := t2.get
  let v1 := t1.get
  v1 + v2
