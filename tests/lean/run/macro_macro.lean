new_frontend

macro mk_m id:ident v:str n:num c:char : command => `(macro $id:ident : term => `(fun (x : String) => x ++ $v ++ toString $n ++ toString $c))

mk_m foo "bla" 10 'a'
mk_m boo "hello" 3 'b'

#check foo "world"
#check boo "boo"
