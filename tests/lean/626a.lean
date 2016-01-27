namespace foo
  definition C₁ := nat
  definition foo (c : C₁) := nat.rec_on c _ _
end foo

namespace boo
  notation `C₁` := nat
  definition foo (c : C₁) := nat.rec_on c _ _
end boo
