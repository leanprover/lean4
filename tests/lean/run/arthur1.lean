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
  | prog .skip ctx k => ret .nil ctx k
  | prog (.eval e) ctx k => expr e ctx k
  | prog (.seq p₁ p₂) ctx k => prog p₁ ctx (.seq p₂ k)
  | prog (.decl n p) ctx k => prog p ctx $ .block ctx (.decl n k)
  | prog (.fork e pT pF) ctx k => expr e ctx (.fork e pT pF k)
  | prog (.loop e p) ctx k => expr e ctx (.loop e p k)
  | prog (.print e) ctx k => expr e ctx (.print k)

  | expr (.lit l) ctx k => ret (.lit l) ctx k
  | expr (.list l) ctx k => ret (.list l) ctx k
  | expr (.var n) ctx k => match ctx[n] with
    | none   => error .name ctx $ notFound n
    | some v => ret v ctx k
  | expr (.lam l) ctx k => ret (.lam l) ctx k
  | expr (.app e es) ctx k => expr e ctx (.app e es k)
  | expr (.unOp o e) ctx k => expr e ctx (.unOp o e k)
  | expr (.binOp o e₁ e₂) ctx k => expr e₁ ctx (.binOp₁ o e₂ k)

  | ret v ctx .exit => done v ctx
  | ret v ctx (.print k) => dbg_trace v; ret .nil ctx k
  | ret _ ctx (.seq p k) => prog p ctx k

  | ret v _ (.block ctx k) => ret v ctx k

  | ret v ctx (.app e es k) => match v with
    | .lam $ .mk ns h p => match h' : consume p ns es with
      | some (some l, p) =>
        ret (.lam $ .mk l (noDupOfConsumeNoDup h h') p) ctx k
      | some (none, p) => prog p ctx (.block ctx k)
      | none => error .runTime ctx $ wrongNParameters e ns.length es.length
    | v                 => error .type ctx $ notAFunction e v

  | ret (.lit $ .bool true)  ctx (.fork _ pT _ k) => prog pT ctx k
  | ret (.lit $ .bool false) ctx (.fork _ _ pF k) => prog pF ctx k
  | ret v ctx (.fork e ..) => error .type ctx $ cantEvalAsBool e v

  | ret (.lit $ .bool true) ctx (.loop e p k) => prog (.seq p (.loop e p)) ctx k
  | ret (.lit $ .bool false) ctx (.loop _ _ k) => ret .nil ctx k
  | ret v ctx (.loop e ..) => error .type ctx $ cantEvalAsBool e v

  | ret v ctx (.decl n k) => ret .nil (ctx.insert n v) k

  | ret v ctx (.unOp o e k) => match v.unOp o with
    | .error m => error .type ctx m
    | .ok    v => ret v ctx k
  | ret v1 ctx (.binOp₁ o e2 k) => expr e2 ctx (.binOp₂ o v1 k)
  | ret v2 ctx (.binOp₂ o v1 k) => match v1.binOp v2 o with
    | .error m => error .type ctx m
    | .ok    v => ret v ctx k

  | s@(error ..) => s
  | s@(done ..)  => s

def Context.equiv (cₗ cᵣ : Context) : Prop :=
  ∀ n : String, cₗ[n] = cᵣ[n]

def State.stepN : State → Nat → State
  | s, 0     => s
  | s, n + 1 => s.step.stepN n

def State.reaches (s₁ s₂ : State) : Prop :=
  ∃ n, s₁.stepN n = s₂

notation cₗ " ≃ " cᵣ:21 => Context.equiv cₗ cᵣ
notation s₁ " ↠ " s₂ => State.reaches s₁ s₂

def State.ctx : State → Context
  | ret   _ c _ => c
  | prog  _ c _ => c
  | expr  _ c _ => c
  | error _ c _ => c
  | done  _ c   => c

theorem Context.equivSelf {c : Context} : c ≃ c :=
  fun _ => rfl

/-
theorem State.skipStep (h : s = (prog .skip c k).step) : s.ctx ≃ c := by
  have : s.ctx = c := by rw [h, step, ctx]
  simp only [this, Context.equivSelf]
-/

theorem State.skipClean : (prog .skip c .exit) ↠ (done .nil c) :=
  ⟨2 , by simp only [stepN, step]⟩
