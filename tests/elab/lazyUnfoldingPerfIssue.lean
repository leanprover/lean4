namespace Ex1

inductive T: Type :=
  | mk: String → Option T → T

def runT: T → Nat
  | .mk _ none => 0
  | .mk _ (some t) => runT t

class Run (α: Type) where
  run: α → Nat
instance: Run T := ⟨runT⟩

def x := T.mk "PrettyLong" (some <| .mk "PrettyLong" none)

theorem equivalent: Run.run x = Run.run x := by
  -- simp (config := { dsimp := false, decide := false, etaStruct := .none }) [Run.run]
  apply Eq.refl (runT x)

example : Run.run x = Run.run x := by
  simp (config := { decide := false }) [Run.run]

end Ex1

namespace Ex2

inductive Wrapper where
  | wrap: Wrapper

def Wrapper.extend: Wrapper → (Unit × Unit)
  | .wrap => ((), ())

mutual
inductive Op where
  | mk: String → Block → Op

inductive Assign where
  | mk : String → Op → Assign

inductive Block where
  | mk: Assign → Block
  | empty: Block
end

mutual
def runOp: Op → Wrapper
  | .mk _ r => let r' := runBlock r; .wrap

def runAssign: Assign → Wrapper
  | .mk _ op => runOp op

def runBlock: Block → Wrapper
  | .mk a => runAssign a
  | .empty => .wrap
end

private def b: Assign := .mk "r" (.mk "APrettyLongString" .empty)

theorem bug: (runAssign b).extend.snd = (runAssign b).extend.snd := by
  --unfold b -- extremely slow
  sorry

end Ex2

namespace Ex3

inductive ProgramType := | Op | Assign | Block

section
set_option hygiene false
notation "Op"     => Program ProgramType.Op
notation "Assign" => Program ProgramType.Assign
notation "Block"  => Program ProgramType.Block
end

inductive Program: (type: ProgramType) → Type :=
  | mkOp: String → Block → Op
  | mkAssign: String → Op → Assign
  | mkBlock: Assign → Block
  | emptyBlock: Block

def runBase: Program type → Nat
  | .mkOp _ v => let _ := runBase v; 0
  | .mkAssign _ t => runBase t
  | .mkBlock u => runBase u
  | .emptyBlock => 0

class Run (α: Type) where
  run: α → Nat
instance: Run Assign := ⟨runBase⟩

def x: Assign := .mkAssign "PrettyLong" <| .mkOp "PrettyLong" .emptyBlock
-- Now runs fine
theorem equivalent: Run.run x = Run.run x := by simp [Run.run]

end Ex3
