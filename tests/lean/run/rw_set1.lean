import data.nat

namespace foo
  attribute nat.add.assoc [simp]
  print nat.add.assoc
end foo

print nat.add.assoc

namespace foo
  print nat.add.assoc
  attribute nat.add.comm [simp]
  open nat
  print "---------"
  print [simp]
end foo
