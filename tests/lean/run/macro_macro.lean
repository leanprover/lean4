macro "mk_m " id:ident v:str n:num c:char : command =>
  let tk := Lean.Syntax.mkStrLit id.getId.toString
  `(macro $tk:str : term => `(fun (x : String) => x ++ $v ++ toString $n ++ toString $c))

#print " ---- "

mk_m foo "bla" 10 'a'
mk_m boo "hello" 3 'b'

/-- info: (fun x => x ++ "bla" ++ toString 10 ++ toString 'a') "world" : String -/
#guard_msgs in
#check foo "world"

/-- info: (fun x => x ++ "hello" ++ toString 3 ++ toString 'b') "boo" : String -/
#guard_msgs in
#check boo "boo"
