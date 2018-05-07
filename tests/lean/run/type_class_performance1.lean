#print usize

set_option pp.all true
set_option trace.class_instances true
set_option trace.type_context.is_def_eq true
set_option trace.type_context.is_def_eq_detail true

def foo1 (a b : uint64) : bool :=
a = b


#exit
def foo2 (a b : uint16) : bool :=
a = b

def foo3 (a b : uint32) : bool :=
a = b

def foo4 (a b : usize) : bool :=
a = b
