namespace old
class is_equiv {A B : Type} (f : A → B) :=
  (inv : B → A)

#check @is_equiv.inv
namespace is_equiv
section
   parameters A B : Type
   parameter  f : A → B
   parameter  c : is_equiv f
   #check inv f
end
end is_equiv
end old
