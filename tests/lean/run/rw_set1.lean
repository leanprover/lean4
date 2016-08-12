constant nat.add_assoc (a b c : nat) : (a + b) + c = a + (b + c)
constant nat.add_comm (a b : nat) : a + b = b + a

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
