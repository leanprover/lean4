inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

infix:67 " :: " => Vector.cons

inductive Ty where
  | int
  | bool
  | fn (a r : Ty)

inductive HasType : Fin n → Vector Ty n → Ty → Type where
  | stop : HasType 0 (ty :: ctx) ty
  | pop  : HasType k ctx ty → HasType k.succ (u :: ctx) ty
                   --^ $/lean/plainTermGoal

inductive Foo : HasType k ctx ty → Prop
                        --^ $/lean/plainTermGoal
