constant nat.add_assoc (a b c : nat) : (a + b) + c = a + (b + c)


namespace foo
  attribute nat.add_assoc [simp]
  print nat.add_assoc
end foo

print nat.add_assoc

namespace foo
  print nat.add_assoc
  attribute nat.add_comm [simp]
  open nat
  print "---------"
  print [simp] simp
end foo
