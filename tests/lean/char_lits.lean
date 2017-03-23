import system.io
open io
#check #"a"

#eval #"a"
#eval #"\n"
#eval #"\\"
variable [io.interface]
#eval put_str (list.cons #"\\" "aaa")
#eval put_str [#"\n"]
#eval put_str [#"\n"]
#eval put_str (list.cons #"\'" "aaa")
