--

def f1.{u} := id.{u}

def f2 : _ := id

def f3.{u} :=
let x := id.{u};
x

def f4 (x) := x

def f5 (x : _) := x

def f6 :=
fun x => x

def f7.{u} :=
let rec x := id.{u};
10
