inductive Foo (α : Type u) where
  | mk1 (val : α)
  | mk2 (left : Foo α) (right : Foo α)
  | mk3 (val : Nat)
  | mk4 (val : String)
  | mk5 (head : α) (tail : Foo α)

@[elab_as_elim]
def Foo.elimCtor1 {motive : Foo α → Sort v} (a : Foo α) (hIdx : a.ctorIdx == 0) (h : (val : α) → motive (Foo.mk1 val)) : motive a :=
  match a with
  | .mk1 a => h a
  | .mk2 .. => Bool.noConfusion hIdx
  | .mk3 .. => Bool.noConfusion hIdx
  | .mk4 .. => Bool.noConfusion hIdx
  | .mk5 .. => Bool.noConfusion hIdx

@[elab_as_elim]
def Foo.elimCtor2 {motive : Foo α → Sort v} (a : Foo α) (hIdx : a.ctorIdx == 1) (h : (left : Foo α) → (right : Foo α) → motive (Foo.mk2 left right)) : motive a :=
  match a with
  | .mk1 .. => Bool.noConfusion hIdx
  | .mk2 left right => h left right
  | .mk3 .. => Bool.noConfusion hIdx
  | .mk4 .. => Bool.noConfusion hIdx
  | .mk5 .. => Bool.noConfusion hIdx

@[elab_as_elim]
def Foo.elimCtor3 {motive : Foo α → Sort v} (a : Foo α) (hIdx : a.ctorIdx == 2) (h : (val : Nat) → motive (Foo.mk3 val)) : motive a :=
  match a with
  | .mk1 .. => Bool.noConfusion hIdx
  | .mk2 .. => Bool.noConfusion hIdx
  | .mk3 val => h val
  | .mk4 .. => Bool.noConfusion hIdx
  | .mk5 .. => Bool.noConfusion hIdx

@[elab_as_elim]
def Foo.elimCtor4 {motive : Foo α → Sort v} (a : Foo α) (hIdx : a.ctorIdx == 3) (h : (val : String) → motive (Foo.mk4 val)) : motive a :=
  match a with
  | .mk1 .. => Bool.noConfusion hIdx
  | .mk2 .. => Bool.noConfusion hIdx
  | .mk3 .. => Bool.noConfusion hIdx
  | .mk4 val => h val
  | .mk5 .. => Bool.noConfusion hIdx

@[elab_as_elim]
def Foo.elimCtor5 {motive : Foo α → Sort v} (a : Foo α) (hIdx : a.ctorIdx == 4) (h : (head : α) → (tail : Foo α) → motive (Foo.mk5 head tail)) : motive a :=
  match a with
  | .mk1 .. => Bool.noConfusion hIdx
  | .mk2 .. => Bool.noConfusion hIdx
  | .mk3 .. => Bool.noConfusion hIdx
  | .mk4 .. => Bool.noConfusion hIdx
  | .mk5 head tail => h head tail

@[reducible] def Foo.noConfusionType' {α : Type u} (P : Sort v) (a b : Foo α) : Sort v :=
  if h : b.ctorIdx == a.ctorIdx then
    match a with
    | .mk1 val1 => Foo.elimCtor1 (motive := fun _ => Sort v) b h (fun val2 => (val1 = val2 → P) → P)
    | .mk2 left1 right1 => Foo.elimCtor2 (motive := fun _ => Sort v) b h (fun left2 right2 => (left1 = left2 → right1 = right2 → P) → P)
    | .mk3 val1 => Foo.elimCtor3 (motive := fun _ => Sort v) b h (fun val2 => (val1 = val2 → P) → P)
    | .mk4 val1 => Foo.elimCtor4 (motive := fun _ => Sort v) b h (fun val2 => (val1 = val2 → P) → P)
    | .mk5 head1 tail1 => Foo.elimCtor5 (motive := fun _ => Sort v) b h (fun head2 tail2 => (head1 = head2 → tail1 = tail2 → P) → P)
  else
    P

@[reducible] def Foo.noConfusion' {α : Type u} {P : Sort u_1} {v1 v2 : Foo α} (h : v1 = v2) : Foo.noConfusionType' P v1 v2 :=
  Eq.ndrec (motive := fun a => v1 = a → Foo.noConfusionType' P v1 a)
    (fun (_ : v1 = v1) =>
      Foo.casesOn v1 (fun _ h => h rfl) (fun _ _ h => h rfl rfl) (fun _ h => h rfl) (fun _ h => h rfl) (fun _ _ h => h rfl rfl))
    h h

def Foo.decEq {α : Type u} [DecidableEq α] (a b : Foo α) : Decidable (a = b) :=
  if hc : b.ctorIdx == a.ctorIdx then
    match a with
    | mk1 val1 => Foo.elimCtor1 b hc fun val2 => if he : val1 = val2 then isTrue (he ▸ rfl) else isFalse (fun h => Foo.noConfusion' h fun h => he h)
    | mk2 left1 right1 => Foo.elimCtor2 b hc fun left2 right2 =>
      match decEq left1 left2 with
      | isTrue he1 => match decEq right1 right2 with
        | isTrue he2 => isTrue (he1 ▸ he2 ▸ rfl)
        | isFalse he2 => isFalse (fun h => Foo.noConfusion' h fun _ h => he2 h)
      | isFalse he1 => isFalse (fun h => Foo.noConfusion' h fun h _ => he1 h)
    | mk3 val1 => Foo.elimCtor3 b hc fun val2 => if he : val1 = val2 then isTrue (he ▸ rfl) else isFalse (fun h => Foo.noConfusion' h fun h => he h)
    | mk4 val1 => Foo.elimCtor4 b hc fun val2 => if he : val1 = val2 then isTrue (he ▸ rfl) else isFalse (fun h => Foo.noConfusion' h fun h => he h)
    | mk5 head1 tail1 => Foo.elimCtor5 b hc fun head2 tail2 =>
      if he1 : head1 = head2 then
        match decEq tail1 tail2 with
        | isTrue he2 => isTrue (he1 ▸ he2 ▸ rfl)
        | isFalse he2 => isFalse (fun h => Foo.noConfusion' h fun _ h => he2 h)
      else
        isFalse (fun h => Foo.noConfusion' h fun h _ => he1 h)
  else
    isFalse (fun h => have : ¬ b.ctorIdx == b.ctorIdx := h ▸ hc; this BEq.rfl)
