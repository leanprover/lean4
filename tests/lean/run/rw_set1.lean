import data.nat

namespace foo
  attribute nat.add.assoc [rewrite]
  print nat.add.assoc
end foo

print nat.add.assoc

namespace foo
  print nat.add.assoc
  attribute nat.add.comm [rewrite]
  open nat
  print "---------"
  print [rewrite]
end foo
