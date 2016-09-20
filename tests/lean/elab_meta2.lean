
print "parametric meta_definition"
meta_definition f {A : Type} : nat → A → A → A
| n a b := if n / 2 = 0 then a else f (n / 2) b a
vm_eval
  if f 10 1 2 = 2 then "OK" else "FAILED"

namespace foo
print "parametric meta_definition inside namespace"
meta_definition bla {A : Type} : nat → A → A → A
| n a b := if n / 2 = 0 then a else bla (n / 2) b a
vm_eval
  if foo.bla 10 1 2 = 2 then "OK" else "FAILED"
end foo

namespace foo
section
print "meta_definition inside parametric scope"
parameter {A : Type}
meta_definition bah : nat → A → A → A
| n a b := if n / 2 = 0 then a else bah (n / 2) b a
vm_eval
  if foo.bah 10 1 2 = 2 then "OK" else "FAILED"
end
end foo

print "private meta_definition"
private meta_definition hprv {A : Type} : nat → A → A → A
| n a b := if n / 2 = 0 then a else hprv (n / 2) b a
vm_eval
  if hprv 10 1 2 = 2 then "OK" else "FAILED"
