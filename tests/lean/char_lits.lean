import system.io

check 'a'

vm_eval 'a'
vm_eval '\n'
vm_eval '\\'
vm_eval put_str (list.cons '\\' "aaa")
vm_eval put_str ['\n']
vm_eval put_str ['\n']
vm_eval put_str (list.cons '\'' "aaa")
