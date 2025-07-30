structure CompoundName where
  module : String
  name : String

structure T where
  name : CompoundName
  placeholder : Nat

/--
Value whose size is bounded by a constant offset of another value.
-/
abbrev Bounded (α : Type _) [SizeOf α] {β} [SizeOf β] (e : β) (c : Int) := { a : α // sizeOf a ≤ sizeOf e + c }

def getArg (e : T) : Bounded T e (-1) := sorry

mutual

inductive A where
| a : A
| b : C → A

inductive C
| c : A → C

end

mutual

def mkA (x : T) : A :=
   match x.name with
   | CompoundName.mk "LongName" "a" => .a
   | CompoundName.mk "LongName" "b" => .a
   | CompoundName.mk "LongName" "c" => .a
   | CompoundName.mk "LongName" "d" => .a
   | CompoundName.mk "LongName" "e" => .a
   | CompoundName.mk "LongName" "f" => .a
   | CompoundName.mk "LongName" "g" => .a
   | CompoundName.mk "LongName" "h" => .a
   | CompoundName.mk "LongName" "i" => .a
   | CompoundName.mk "LongName" "j" => .a
   | CompoundName.mk "LongName" "k" => .a
   | CompoundName.mk "LongName" "z" =>
      let ⟨y, _⟩ := getArg x
      .b (mkC y)
   | _ => sorry
termination_by sizeOf x

def mkC (x : T) : C :=
  match x.name with
  | CompoundName.mk "LongName" "b" =>
    let ⟨y, _⟩ := getArg x
    .c (mkA y)
  | f => sorry
termination_by sizeOf x

end
