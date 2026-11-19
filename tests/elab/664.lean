set_option warn.classDefReducibility false

class A (α : Type _) where  a : α → Unit

instance : A Empty where a x := nomatch x

def test : A Empty where a x := nomatch x
