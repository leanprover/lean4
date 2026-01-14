inductive Vector' (α : Type u) : Nat → Type u
  | nil : Vector' α 0
  | cons : α → Vector' α n → Vector' α (n+1)

infix:67 " :: " => Vector'.cons

inductive Ty where
  | int
  | bool
  | fn (a r : Ty)

inductive HasType : Fin n → Vector' Ty n → Ty → Type where
  | stop : HasType 0 (ty :: ctx) ty
  | pop  : HasType k ctx ty → HasType k.succ (u :: ctx) ty
                   --^ $/lean/plainTermGoal

inductive Foo : HasType k ctx ty → Prop
                        --^ $/lean/plainTermGoal

def foo : HasType k ctx ty → Prop
                  --^ $/lean/plainTermGoal
  | _ => True

structure Ex where
  aux : HasType k ctx ty
                --^ $/lean/plainTermGoal
  boo : HasType k ctx ty → Prop := fun _ => True
                --^ $/lean/plainTermGoal

variable (x : HasType k ctx ty)
                      --^ $/lean/plainTermGoal

#check x
