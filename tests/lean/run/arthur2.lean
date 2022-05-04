import Std

inductive NEList (α : Type)
  | uno  : α → NEList α
  | cons : α → NEList α → NEList α

def NEList.contains [BEq α] : NEList α → α → Bool
  | uno  a,    x => a == x
  | cons a as, x => a == x || as.contains x

def NEList.noDup [BEq α] : NEList α → Bool
  | uno  a    => true
  | cons a as => ¬as.contains a && as.noDup

@[specialize]
def NEList.foldl (f : α → β → α) : (init : α) → NEList β → α
  | a, uno  b   => f a b
  | a, cons b l => foldl f (f a b) l

@[specialize]
def NEList.map (f : α → β) : NEList α → NEList β
  | uno  a     => uno  (f a)
  | cons a  as => cons (f a) (map f as)

inductive Literal
  | bool  : Bool   → Literal
  | int   : Int    → Literal
  | float : Float  → Literal
  | str   : String → Literal

inductive BinOp
  | add | mul | eq | ne | lt | le | gt | ge

inductive UnOp
  | not

mutual

  inductive Lambda
    | mk : (l : NEList String) → l.noDup → Program → Lambda

  inductive Expression
    | lit   : Literal → Expression
    | var   : String → Expression
    | lam   : Lambda → Expression
    | list  : List Literal → Expression
    | app   : Expression → NEList Expression → Expression
    | unOp  : UnOp  → Expression → Expression
    | binOp : BinOp → Expression → Expression → Expression

  inductive Program
    | skip  : Program
    | eval  : Expression → Program
    | decl  : String  → Program → Program
    | seq   : Program → Program → Program
    | fork  : Expression → Program → Program → Program
    | loop  : Expression → Program → Program
    | print : Expression → Program
    deriving Inhabited

end

inductive Value
  | nil  : Value
  | lit  : Literal → Value
  | list : List Literal → Value
  | lam  : Lambda → Value
  deriving Inhabited

abbrev Context := Std.HashMap String Value

inductive ErrorType
  | name | type | runTime

def Literal.typeStr : Literal → String
  | bool  _ => "bool"
  | int   _ => "int"
  | float _ => "float"
  | str   _ => "str"

def removeRightmostZeros (s : String) : String :=
  let rec aux (buff res : List Char) : List Char → List Char
    | []      => res.reverse
    | a :: as =>
      if a != '0'
        then aux [] (a :: (buff ++ res)) as
        else aux (a :: buff) res as
  ⟨aux [] [] s.data⟩

protected def Literal.toString : Literal → String
  | bool  b => toString b
  | int   i => toString i
  | float f => removeRightmostZeros $ toString f
  | str   s => s

def Lambda.typeStr : Lambda → String
  | mk l .. => (l.foldl (init := "") fun acc _ => acc ++ "_ → ") ++ "_"

def Value.typeStr : Value → String
  | nil    => "nil"
  | lit  l => l.typeStr
  | list _ => "list"
  | lam  l => l.typeStr

def Literal.eq : Literal → Literal → Bool
  | bool  bₗ, bool  bᵣ => bₗ == bᵣ
  | int   iₗ, int   iᵣ => iₗ == iᵣ
  | float fₗ, float fᵣ => fₗ == fᵣ
  | int   iₗ, float fᵣ => (.ofInt iₗ) == fᵣ
  | float fₗ, int   iᵣ => fₗ == (.ofInt iᵣ)
  | str   sₗ, str   sᵣ => sₗ == sᵣ
  | _       , _        => false

def listLiteralEq : List Literal → List Literal → Bool
  | [], [] => true
  | a :: a' :: as, b :: b' :: bs =>
    a.eq b && listLiteralEq (a' :: as) (b' :: bs)
  | _, _   => false

def opError (app l r : String) : String :=
  s!"I can't perform a '{app}' operation between '{l}' and '{r}'"

def opError1 (app v : String) : String :=
  s!"I can't perform a '{app}' operation on '{v}'"

def Value.not : Value → Except String Value
  | lit $ .bool b => return lit $ .bool !b
  | v             => throw $ opError1 "!" v.typeStr

def Value.add : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ || bᵣ
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .int  $ iₗ +  iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .float $ fₗ +  fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .float $ (.ofInt iₗ) +  fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .float $ fₗ +  (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .str   $ sₗ ++ sᵣ
  | list         lₗ, list         lᵣ => return list  $ lₗ ++ lᵣ
  | list         l,  lit          r  => return list  $ l.concat r
  | l,               r               => throw $ opError "+" l.typeStr r.typeStr

def Value.mul : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return .lit $ .bool  $ bₗ && bᵣ
  | lit $ .int   iₗ, lit $ .int   iᵣ => return .lit $ .int   $ iₗ *  iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return .lit $ .float $ fₗ *  fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return .lit $ .float $ (.ofInt iₗ) *  fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return .lit $ .float $ fₗ *  (.ofInt iᵣ)
  | l,               r               => throw $ opError "*" l.typeStr r.typeStr

def Bool.toNat : Bool → Nat
  | false => 0
  | true  => 1

def Value.lt : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat < bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ < iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ < fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) < fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ < (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ < sᵣ
  | list lₗ, list lᵣ => return lit $ .bool $ lₗ.length < lᵣ.length
  | l,               r               => throw $ opError "<" l.typeStr r.typeStr

def Value.le : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat ≤ bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ ≤ iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ ≤ fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) ≤ fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ ≤ (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ < sᵣ || sₗ == sᵣ
  | list lₗ, list  lᵣ => return lit $ .bool $ lₗ.length ≤ lᵣ.length
  | l,         r      => throw $ opError "<=" l.typeStr r.typeStr

def Value.gt : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat > bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ > iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ > fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) > fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ > (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ > sᵣ
  | list lₗ, list lᵣ => return lit $ .bool $ lₗ.length > lᵣ.length
  | l,       r       => throw $ opError ">" l.typeStr r.typeStr

def Value.ge : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat ≥ bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ ≥ iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ ≥ fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) ≥ fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ ≥ (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ > sᵣ || sₗ == sᵣ
  | list lₗ, list  lᵣ => return lit $ .bool $ lₗ.length ≥ lᵣ.length
  | l,       r        => throw $ opError ">=" l.typeStr r.typeStr

def Value.eq : Value → Value → Except String Value
  | nil,     nil      => return lit $ .bool true
  | lit  lₗ, lit lᵣ   => return lit $ .bool $ lₗ.eq lᵣ
  | list lₗ, list  lᵣ => return lit $ .bool (listLiteralEq lₗ lᵣ)
  | lam .. , lam ..   => throw "I can't compare functions"
  | _,       _        => return lit $ .bool false

def Value.ne : Value → Value → Except String Value
  | nil,     nil      => return lit $ .bool false
  | lit  lₗ, lit lᵣ   => return lit $ .bool $ !(lₗ.eq lᵣ)
  | list lₗ, list  lᵣ => return lit $ .bool !(listLiteralEq lₗ lᵣ)
  | lam ..,  lam ..   => throw "I can't compare functions"
  | _,       _        => return lit $ .bool true

def Value.unOp : Value → UnOp → Except String Value
  | v, .not => v.not

def Value.binOp : Value → Value → BinOp → Except String Value
  | l, r, .add => l.add r
  | l, r, .mul => l.mul r
  | l, r, .lt  => l.lt r
  | l, r, .le  => l.le r
  | l, r, .gt  => l.gt r
  | l, r, .ge  => l.ge r
  | l, r, .eq  => l.eq r
  | l, r, .ne  => l.ne r

def NEList.unfoldStrings (l : NEList String) : String :=
  l.foldl (init := "") $ fun acc a => acc ++ s!" {a}" |>.trimLeft

mutual

  partial def unfoldExpressions (es : NEList Expression) : String :=
    (es.map exprToString).unfoldStrings

  partial def exprToString : Expression → String
    | .var  n    => n
    | .lit  l    => l.toString
    | .list l    => toString $ l.map Literal.toString
    | .lam  _    => "«function»"
    | .app  e es => s!"({exprToString e} {unfoldExpressions es})"
    | .unOp  .not e   => s!"!{exprToString e}"
    | .binOp .add l r => s!"({exprToString l} + {exprToString r})"
    | .binOp .mul l r => s!"({exprToString l} * {exprToString r})"
    | .binOp .eq  l r => s!"({exprToString l} = {exprToString r})"
    | .binOp .ne  l r => s!"({exprToString l} != {exprToString r})"
    | .binOp .lt  l r => s!"({exprToString l} < {exprToString r})"
    | .binOp .le  l r => s!"({exprToString l} <= {exprToString r})"
    | .binOp .gt  l r => s!"({exprToString l} > {exprToString r})"
    | .binOp .ge  l r => s!"({exprToString l} >= {exprToString r})"

end

instance : ToString Expression := ⟨exprToString⟩

def valToString : Value → String
    | .nil    => "«nil»"
    | .lit  l => l.toString
    | .list l => toString $ l.map Literal.toString
    | .lam  _ => "«function»"

instance : ToString Value := ⟨valToString⟩

def consume (p : Program) :
    NEList String → NEList Expression →
      Option ((Option (NEList String)) × Program)
  | .cons n ns, .cons e es => consume (.seq (.decl n (.eval e)) p) ns es
  | .cons n ns, .uno  e    => some (some ns, .seq (.decl n (.eval e)) p)
  | .uno  n,    .uno  e    => some (none, .seq (.decl n (.eval e)) p)
  | .uno  _,    .cons ..   => none

theorem noDupOfConsumeNoDup
  (h : ns.noDup) (h' : consume p' ns es = some (some l, p)) :
    l.noDup = true := by
  induction ns generalizing p' es with
  | uno  _      => cases es <;> cases h'
  | cons _ _ hi =>
    simp [NEList.noDup] at h
    cases es with
    | uno  _   => simp [consume] at h'; simp only [h.2, ← h'.1]
    | cons _ _ => exact hi h.2 h'

inductive Continuation
  | exit   : Continuation
  | seq    : Program → Continuation → Continuation
  | decl   : String → Continuation → Continuation
  | fork   : Expression → Program → Program → Continuation → Continuation
  | loop   : Expression → Program → Continuation → Continuation
  | unOp   : UnOp → Expression → Continuation → Continuation
  | binOp₁ : BinOp → Expression → Continuation → Continuation
  | binOp₂ : BinOp → Value → Continuation → Continuation
  | app    : Expression → NEList Expression → Continuation → Continuation
  | block  : Context → Continuation → Continuation
  | print  : Continuation → Continuation

inductive State
  | ret   : Value      → Context → Continuation → State
  | prog  : Program    → Context → Continuation → State
  | expr  : Expression → Context → Continuation → State
  | error : ErrorType  → Context → String → State
  | done  : Value      → Context → State

def cantEvalAsBool (e : Expression) (v : Value) : String :=
  s!"I can't evaluate '{e}' as a 'bool' because it reduces to '{v}', of " ++
    s!"type '{v.typeStr}'"

def notFound (n : String) : String :=
  s!"I can't find the definition of '{n}'"

def notAFunction (e : Expression) (v : Value) : String :=
  s!"I can't apply arguments to '{e}' because it evaluates to '{v}', of " ++
    s!"type '{v.typeStr}'"

def wrongNParameters (e : Expression) (allowed provided : Nat) : String :=
  s!"I can't apply {provided} arguments to '{e}' because the maximum " ++
    s!"allowed is {allowed}"

def NEList.length : NEList α → Nat
  | uno  _   => 1
  | cons _ l => 1 + l.length

def State.step : State → State
  | prog .skip c k => ret .nil c k
  | prog (.eval e) c k => expr e c k
  | prog (.seq p₁ p₂) c k => prog p₁ c (.seq p₂ k)
  | prog (.decl n p) c k => prog p c $ .block c (.decl n k)
  | prog (.fork e pT pF) c k => expr e c (.fork e pT pF k)
  | prog (.loop e p) c k => expr e c (.loop e p k)
  | prog (.print e) c k => expr e c (.print k)

  | expr (.lit l) c k => ret (.lit l) c k
  | expr (.list l) c k => ret (.list l) c k
  | expr (.var n) c k => match c[n] with
    | none   => error .name c $ notFound n
    | some v => ret v c k
  | expr (.lam l) c k => ret (.lam l) c k
  | expr (.app e es) c k => expr e c (.app e es k)
  | expr (.unOp o e) c k => expr e c (.unOp o e k)
  | expr (.binOp o e₁ e₂) c k => expr e₁ c (.binOp₁ o e₂ k)

  | ret v c .exit => done v c
  | ret v c (.print k) => dbg_trace v; ret .nil c k
  | ret _ c (.seq p k) => prog p c k

  | ret v _ (.block c k) => ret v c k

  | ret v c (.app e es k) => match v with
    | .lam $ .mk ns h p => match h' : consume p ns es with
      | some (some l, p) =>
        ret (.lam $ .mk l (noDupOfConsumeNoDup h h') p) c k
      | some (none, p) => prog p c (.block c k)
      | none => error .runTime c $ wrongNParameters e ns.length es.length
    | v                 => error .type c $ notAFunction e v

  | ret (.lit $ .bool true)  c (.fork _ pT _ k) => prog pT c k
  | ret (.lit $ .bool false) c (.fork _ _ pF k) => prog pF c k
  | ret v c (.fork e ..) => error .type c $ cantEvalAsBool e v

  | ret (.lit $ .bool true) c (.loop e p k) => prog (.seq p (.loop e p)) c k
  | ret (.lit $ .bool false) c (.loop _ _ k) => ret .nil c k
  | ret v c (.loop e ..) => error .type c $ cantEvalAsBool e v

  | ret v c (.decl n k) => ret .nil (c.insert n v) k

  | ret v c (.unOp o e k) => match v.unOp o with
    | .error m => error .type c m
    | .ok    v => ret v c k
  | ret v₁ c (.binOp₁ o e₂ k) => expr e₂ c (.binOp₂ o v₁ k)
  | ret v₂ c (.binOp₂ o v₁ k) => match v₁.binOp v₂ o with
    | .error m => error .type c m
    | .ok    v => ret v c k

  | s@(error ..) => s
  | s@(done ..)  => s

def State.isProg : State → Bool
  | prog .. => true
  | _       => false

def State.isEnd : State → Bool
  | done  .. => true
  | error .. => true
  | _        => false

def State.stepN : State → Nat → State
  | s, 0     => s
  | s, n + 1 => s.step.stepN n

notation s "^" "[" n "]" => State.stepN s n

theorem State.retProgression :
    ∃ n, (ret v c k^[n]).isEnd ∨ (ret v c k^[n]).isProg := by
  induction k generalizing v c with
  | app e es k hi =>
    cases v with
    | lam lm =>
      cases lm with
      | mk ns h p =>
        exists 1
        simp [stepN, step] -- doesn't seem to use `
        split
        next l p' h' => simp!; sorry
        next => simp!
        next => simp!
    | _ => exact ⟨1, by simp [stepN, step, isEnd]⟩
  | _ => sorry

#check @State.step.match_2.eq_1
#check @State.step.match_2.eq_2
#check @State.step.match_2.eq_3
#check @State.step.match_2.splitter
