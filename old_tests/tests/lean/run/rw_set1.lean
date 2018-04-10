namespace foo
  attribute [simp] nat.add_assoc
  #print nat.add_assoc
end foo

#print nat.add_assoc

namespace foo
  #print nat.add_assoc
  attribute [simp] nat.add_comm
  open nat
  #print "---------"
  #print [simp] default
end foo
