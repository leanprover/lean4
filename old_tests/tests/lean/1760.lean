section
parameter big_type : Type 1
parameter x : big_type
parameter f {A : Type} : A → bool

def foo : bool := f x
end
