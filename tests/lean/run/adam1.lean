inductive BinOp where
  | plus
  | times

inductive Expr where
  | const : Nat → Expr
  | binOp : BinOp → Expr → Expr → Expr

def BinOp.denote (op : BinOp) : Nat → Nat → Nat :=
  match op with
  | plus  => Nat.add
  | times => Nat.mul

def Expr.denote (e : Expr) : Nat :=
  match e with
  | const v      => v
  | binOp op a b => op.denote a.denote b.denote

#eval Expr.denote (Expr.const 42)
#eval Expr.denote (.const 42)
#eval Expr.denote <| .const 42
#eval Expr.denote <| .binOp .plus (.const 2) (.const 3)
#eval Expr.denote <| .binOp .times (.const 2) (.const 3)

#eval (.binOp .times (.binOp .plus (.const 4) (.const 2)) (.const 3) : Expr).denote

def e₁ : Expr := .binOp .times (.binOp .plus (.const 4) (.const 2)) (.const 3)

example : e₁.denote = 18 :=
  rfl

inductive Instr where
  | const : Nat → Instr
  | binOp : BinOp → Instr

abbrev Prog := List Instr
abbrev Stack := List Nat

def Instr.denote (i : Instr) (s : Stack) : Option Stack :=
  match i, s with
  | const v, s         => some (v :: s)
  | binOp op, a::b::s' => some (op.denote a b :: s')
  | _, _               => none

def Prog.denote (p : Prog) (s : Stack) : Option Stack :=
  match p with
  | [] => some s
  | i :: (p' : Prog) =>
    match i.denote s with
    | none    => none
    | some s' => p'.denote s'

def Expr.compile (e : Expr) : Prog :=
  match e with
  | const v      => [.const v]
  | binOp op a b => b.compile ++ a.compile ++ [.binOp op]

theorem compile_correct' (e : Expr) (p : Prog) (s : Stack) : (e.compile ++ p : Prog).denote s = p.denote (e.denote :: s) := by
  induction e generalizing p s with
  | const => rfl
  | binOp => simp [Expr.compile, Expr.denote, Prog.denote, Instr.denote, List.append_assoc, *]

theorem compile_correct (e : Expr) : e.compile.denote [] = some [e.denote] := by
  have := compile_correct' e [] []
  simp [Prog.denote] at this
  assumption
