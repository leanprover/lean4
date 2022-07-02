def MyArray := Array

namespace MyArray

def getOp? (self : MyArray α) (idx : Nat) : Option α :=
  Array.get? self idx

def getOp! [Inhabited α] (self : MyArray α) (idx : Nat) : α :=
  Array.get! self idx

def getOp (self : MyArray α) (idx : Fin self.size) : α :=
  Array.get self idx

end MyArray

variable (a : MyArray Nat)

#check a[0]!
#check a[0]?

variable (i : Fin a.size)
#check a[i]
