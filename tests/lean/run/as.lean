namespace foo
  definition id {A : Type} (a : A) := a
  definition pr1 {A : Type} (a b : A) := a
end foo

open foo as bla (hiding pr1)
check bla.id

open foo as bla (renaming pr1→pr)
check bla.pr
print raw bla.id

open foo as boo (pr1)
check boo.pr1

open foo as boooo (renaming pr1→pr) (hiding id)
check boooo.pr

namespace foo
namespace bla
  definition pr2 {A : Type} (a b : A) := b
end bla
end foo

open foo.bla as bb
check bb.pr2
