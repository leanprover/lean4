macro "mk_m " id:ident v:str n:num c:char : command =>
  let tk : Lean.Syntax := Lean.Syntax.mkStrLit id.getId.toString
  `(macro $tk:strLit : term => `(fun (x : String) => x ++ $v ++ toString $n ++ toString $c))

#print " ---- "

mk_m foo "bla" 10 'a'
mk_m boo "hello" 3 'b'

#check foo "world"
#check boo "boo"
