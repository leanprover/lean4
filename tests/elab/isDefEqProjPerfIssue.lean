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
