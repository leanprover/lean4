section
set_option pp.annotations true
parameters {α : Type} [has_to_string α]
def f (a : α) : string := to_string a
def g  := f
def g' := (f, α)
def h  := (f, g, g', α)

#print f
#print g
#print g'
#print h

end
