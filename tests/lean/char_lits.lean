import system.io
open io
#check 'a'
#check '\\'
#check 'α'

#eval 'a'
#eval '\n'
#eval '\\'

#eval put_str ("aaa".str '\\')
#eval put_str $ repr '\n'
#eval put_str $ string.singleton '\n'
#eval put_str ("aaa".str '\'')

#check ['\x7f', '\x00', '\x11']
-- ^^ all characters should be pretty-printed using \x escapes

#eval 'α'
#eval 'β'
#eval '\u03B1'
#eval '\u03B2'
