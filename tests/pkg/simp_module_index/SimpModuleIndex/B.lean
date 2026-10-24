import SimpModuleIndex.A

namespace SMI

-- shares the root key `f` with `A`
@[simp] theorem f_one : f 1 = 2 := rfl
-- re-adding replaces the entry from `A` in place
attribute [simp 2000] f_zero
-- adding the converse erases the forward theorem from `A`
attribute [simp ←] p_q

-- re-adding an instance from `A` with a new priority overrides its entry
attribute [instance 2000] instCNat2
-- a declaration from `A` becomes an instance
attribute [instance] instCInt

end SMI
