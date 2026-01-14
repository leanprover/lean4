namespace Foo

def x := 10

scoped macro "~0~" : term => `(0)

#check ~0~

end Foo

open Foo hiding x -- must open scoped notation and attributes too

#check ~0~
