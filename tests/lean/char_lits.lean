import system.io
open io
#check 'a'

#eval 'a'
#eval '\n'
#eval '\\'
variable [io.interface]
#eval put_str ("aaa".str '\\')
#eval put_str '\n'.to_string
#eval put_str $ string.singleton '\n'
#eval put_str ("aaa".str '\'')
