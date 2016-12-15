print "parametric meta definition"
meta definition f {A : Type} : nat → A → A → A
| n a b := if n / 2 = 0 then a else f (n / 2) b a
vm_eval
  if f 10 1 2 = 2 then "OK" else "FAILED"

namespace foo
print "parametric meta definition inside namespace"
meta definition bla {A : Type} : nat → A → A → A
| n a b := if n / 2 = 0 then a else bla (n / 2) b a
vm_eval
  if foo.bla 10 1 2 = 2 then "OK" else "FAILED"
end foo

namespace foo
section
print "meta definition inside parametric scope"
parameter {A : Type}
meta definition bah : nat → A → A → A
| n a b := if n / 2 = 0 then a else bah (n / 2) b a
end
vm_eval if foo.bah 10 1 2 = 2 then "OK" else "FAILED"
end foo

print "private meta definition"
private meta definition hprv {A : Type} : nat → A → A → A
| n a b := if n / 2 = 0 then a else hprv (n / 2) b a
vm_eval
  if hprv 10 1 2 = 2 then "OK" else "FAILED"
