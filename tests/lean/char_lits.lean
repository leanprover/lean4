import system.io
open io
#check #"a"

#eval #"a"
#eval #"\n"
#eval #"\\"
#eval put_str (list.cons #"\\" "aaa")
#eval put_str [#"\n"]
#eval put_str [#"\n"]
#eval put_str (list.cons #"\'" "aaa")
