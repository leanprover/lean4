namespace foo
  definition C¹ := nat
  definition foo (c : C¹) := nat.rec_on c _ _
end foo

namespace boo
  notation `C¹` := nat
  definition foo (c : C¹) := nat.rec_on c _ _
end boo
