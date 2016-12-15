import system.io

def tst : io unit :=
   put_str "hello\n"
>> put_str "world\n"
>> put_str "from Lean\n"

vm_eval tst
