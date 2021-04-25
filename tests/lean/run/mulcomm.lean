class MulComm (α : Type u) [Mul α] : Prop where
    mulComm : {a b : α} → a * b = b * a

instance : Mul Bool where
  mul := and

instance : MulComm Bool where
  mulComm {a b} :=
    match a, b with
    | true, true   => rfl
    | true, false  => rfl
    | false, true  => rfl
    | false, false => rfl

instance : MulComm Bool where
  mulComm := fun {a b} =>
    match a, b with
    | true, true   => rfl
    | true, false  => rfl
    | false, true  => rfl
    | false, false => rfl

instance : MulComm Bool := {
  mulComm := fun {a b} =>
    match a, b with
    | true, true   => rfl
    | true, false  => rfl
    | false, true  => rfl
    | false, false => rfl
}

instance : MulComm Bool := {
  mulComm := @fun a b =>
    match a, b with
    | true, true   => rfl
    | true, false  => rfl
    | false, true  => rfl
    | false, false => rfl
}

instance : MulComm Bool where
  mulComm {a b} := by cases a <;> cases b <;> rfl

instance : MulComm Bool :=
  ⟨by intro a b; cases a <;> cases b <;> rfl⟩

instance : MulComm Bool :=
  ⟨fun {a b} => by cases a <;> cases b <;> rfl⟩

instance : MulComm Bool :=
  ⟨fun {a b} =>
    match a, b with
    | true, true   => rfl
    | true, false  => rfl
    | false, true  => rfl
    | false, false => rfl⟩

instance : MulComm Bool :=
  ⟨@fun a b =>
    match a, b with
    | true, true   => rfl
    | true, false  => rfl
    | false, true  => rfl
    | false, false => rfl⟩
