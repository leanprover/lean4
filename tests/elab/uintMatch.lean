def f : UInt8 → Bool
 | 5 => true
 | _ => false

#eval f 8
#eval f 5

def g : UInt32 → String
 | 5    => "hello"
 | 1555 => "world"
 | _    => "bla"

#eval g 5
#eval g 1555
#eval g 555
