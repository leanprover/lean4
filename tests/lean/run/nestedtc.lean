variable {α : Type}
variable {R : Type}

class Zip (α : Type) -- represents `Zero`

class SMul (R : Type) (α : Type) where
  smul : R → α → α

infixr:73 " • " => SMul.smul

class MulAction (R : Type) (β : Type) extends SMul R β

class SMulZeroClass (R α : Type) extends SMul R α where
  smul_zero : ∀ r : R, ∀ a : α, r • a = a

class MulActionWithZero (R α : Type) extends MulAction R α, SMulZeroClass R α

class SMulWithZero (R α : Type) [Zip R] [Zip α] extends SMulZeroClass R α

instance MulActionWithZero.toSMulWithZero (R M : Type)
    [Zip R] [Zip M] [m : MulActionWithZero R M] :
    SMulWithZero R M :=
  { m with }


namespace pi
variable {I : Type}
variable {f : I → Type}

instance instZero [∀ i, Zip (f i)] : Zip (∀ i : I, f i) := ⟨⟩

instance instSMul [∀ i, SMul R (f i)] : SMul R (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

instance smulWithZero (R) [Zip R] [∀ i, Zip (f i)] [∀ i, SMulWithZero R (f i)] :
    SMulWithZero R (∀ i, f i) :=
  { pi.instSMul with
    smul_zero := sorry }

instance mulAction (R) [∀ i, MulAction R (f i)] : MulAction R (∀ i : I, f i) where
  smul := (· • ·)

instance mulActionWithZero (R) [Zip R] [∀ i, Zip (f i)] [∀ i, MulActionWithZero R (f i)] :
    MulActionWithZero R (∀ i, f i) :=
 { pi.mulAction _, pi.smulWithZero _ with }
