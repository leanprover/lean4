set_option pp.notation false

#check `foo
#check `foo.bla
#check `«foo bla»
#check `«foo bla».«hello world»
#check `«foo bla».boo.«hello world»
#check `foo.«hello»

macro "dummy1" : term => `(`hello)
macro "dummy2" : term => `(`hello.«world !!!»)

#check dummy1
#check dummy2
