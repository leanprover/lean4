universes u v
class module (α : out_param $ Type u) (β : Type v) [out_param $ ring α] extends add_comm_group β :=
(foo : β → nat)

-- both α and `ring α` should be implicit (_not_ instance implicit)
#print module.to_add_comm_group
