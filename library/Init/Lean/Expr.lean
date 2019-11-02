/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Level
import Init.Lean.KVMap
import Init.Data.HashMap
import Init.Data.HashSet
import Init.Data.PersistentHashMap
import Init.Data.PersistentHashSet

namespace Lean

inductive Literal
| natVal (val : Nat)
| strVal (val : String)

inductive BinderInfo
| default | implicit | strictImplicit | instImplicit | auxDecl

namespace BinderInfo

def isInstImplicit : BinderInfo → Bool
| instImplicit => true
| _            => false

def isAuxDecl : BinderInfo → Bool
| auxDecl => true
| _       => false

protected def beq : BinderInfo → BinderInfo → Bool
| default,        default        => true
| implicit,       implicit       => true
| strictImplicit, strictImplicit => true
| instImplicit,   instImplicit   => true
| auxDecl,        auxDecl        => true
| _,              _              => false

instance : HasBeq BinderInfo := ⟨BinderInfo.beq⟩

end BinderInfo

abbrev MData := KVMap
namespace MData
abbrev empty : MData := {KVMap .}
instance : HasEmptyc MData := ⟨empty⟩
end MData

/- We use the `E` suffix (short for `Expr`) to avoid collision with keywords.
   We considered using «...», but it is too inconvenient to use. -/
inductive Expr
| bvar    : Nat → Expr                                -- bound variables
| fvar    : Name → Expr                               -- free variables
| mvar    : Name → Expr                               -- meta variables
| sort    : Level → Expr                              -- Sort
| const   : Name → List Level → Expr                  -- constants
| app     : Expr → Expr → Expr                        -- application
| lam     : Name → BinderInfo → Expr → Expr → Expr    -- lambda abstraction
| forallE : Name → BinderInfo → Expr → Expr → Expr    -- (dependent) arrow
| letE    : Name → Expr → Expr → Expr → Expr          -- let expressions
| lit     : Literal → Expr                            -- literals
| mdata   : MData → Expr → Expr                       -- metadata
| proj    : Name → Nat → Expr → Expr                  -- projection

instance exprIsInhabited : Inhabited Expr :=
⟨Expr.sort Level.zero⟩

attribute [extern "lean_expr_mk_bvar"]   Expr.bvar
attribute [extern "lean_expr_mk_fvar"]   Expr.fvar
attribute [extern "lean_expr_mk_mvar"]   Expr.mvar
attribute [extern "lean_expr_mk_sort"]   Expr.sort
attribute [extern "lean_expr_mk_const"]  Expr.const
attribute [extern "lean_expr_mk_app"]    Expr.app
attribute [extern "lean_expr_mk_lambda"] Expr.lam
attribute [extern "lean_expr_mk_forall"] Expr.forallE
attribute [extern "lean_expr_mk_let"]    Expr.letE
attribute [extern "lean_expr_mk_lit"]    Expr.lit
attribute [extern "lean_expr_mk_mdata"]  Expr.mdata
attribute [extern "lean_expr_mk_proj"]   Expr.proj

-- deprecated Constructor
@[extern "lean_expr_local"]
constant Expr.local (n : Name) (pp : Name) (ty : Expr) (bi : BinderInfo) : Expr := default _

def mkApp (f : Expr) (args : Array Expr) : Expr :=
args.foldl Expr.app f

private partial def mkAppRangeAux (n : Nat) (args : Array Expr) : Nat → Expr → Expr
| i, e => if i < n then mkAppRangeAux (i+1) (Expr.app e (args.get! i)) else e

/-- `mkAppRange f i j #[a_1, ..., a_i, ..., a_j, ... ]` ==> the expression `f a_i ... a_{j-1}` -/
def mkAppRange (f : Expr) (i j : Nat) (args : Array Expr) : Expr :=
mkAppRangeAux j args i f

def mkCApp (fn : Name) (args : Array Expr) : Expr :=
mkApp (Expr.const fn []) args

def mkAppRev (fn : Expr) (revArgs : Array Expr) : Expr :=
revArgs.foldr (fun a r => Expr.app r a) fn

namespace Expr
@[extern "lean_expr_hash"]
constant hash (n : @& Expr) : USize := default USize

instance : Hashable Expr := ⟨Expr.hash⟩

-- TODO: implement it in Lean
@[extern "lean_expr_dbg_to_string"]
constant dbgToString (e : @& Expr) : String := default String

@[extern "lean_expr_quick_lt"]
constant quickLt (a : @& Expr) (b : @& Expr) : Bool := default _

@[extern "lean_expr_lt"]
constant lt (a : @& Expr) (b : @& Expr) : Bool := default _

/- Return true iff `a` and `b` are alpha equivalent.
   Binder annotations are ignored. -/
@[extern "lean_expr_eqv"]
constant eqv (a : @& Expr) (b : @& Expr) : Bool := default _

instance : HasBeq Expr := ⟨Expr.eqv⟩

/- Return true iff `a` and `b` are equal.
   Binder names and annotations are taking into account. -/
@[extern "lean_expr_equal"]
constant equal (a : @& Expr) (b : @& Expr) : Bool := default _

@[extern "lean_expr_has_expr_mvar"]
constant hasExprMVar (a : @& Expr) : Bool := default _

@[extern "lean_expr_has_level_mvar"]
constant hasLevelMVar (a : @& Expr) : Bool := default _

@[inline] def hasMVar (a : Expr) : Bool :=
a.hasExprMVar || a.hasLevelMVar

@[extern "lean_expr_has_fvar"]
constant hasFVar (a : @& Expr) : Bool := default _

def isSort : Expr → Bool
| sort _ => true
| _      => false

def isBVar : Expr → Bool
| bvar _ => true
| _      => false

def isMVar : Expr → Bool
| mvar _ => true
| _      => false

def isFVar : Expr → Bool
| fvar _ => true
| _      => false

def isApp : Expr → Bool
| app _ _ => true
| _       => false

def isProj : Expr → Bool
| proj _ _ _ => true
| _          => false

def isConst : Expr → Bool
| const _ _ => true
| _         => false

def isConstOf : Expr → Name → Bool
| const n _, m => n == m
| _,         _ => false

def isForall : Expr → Bool
| forallE _ _ _ _ => true
| _               => false

def isLambda : Expr → Bool
| lam _ _ _ _ => true
| _           => false

def isBinding : Expr → Bool
| lam _ _ _ _     => true
| forallE _ _ _ _ => true
| _               => false

def isLet : Expr → Bool
| letE _ _ _ _ => true
| _            => false

def isMData : Expr → Bool
| mdata _ _ => true
| _         => false

def getAppFn : Expr → Expr
| app f a => getAppFn f
| e       => e

def getAppNumArgsAux : Expr → Nat → Nat
| app f a, n => getAppNumArgsAux f (n+1)
| e,       n => n

def getAppNumArgs (e : Expr) : Nat :=
getAppNumArgsAux e 0

private def getAppArgsAux : Expr → Array Expr → Nat → Array Expr
| app f a, as, i => getAppArgsAux f (as.set! i a) (i-1)
| _,       as, _ => as

@[inline] def getAppArgs (e : Expr) : Array Expr :=
let dummy := Expr.sort Level.zero;
let nargs := e.getAppNumArgs;
getAppArgsAux e (mkArray nargs dummy) (nargs-1)

private def getAppRevArgsAux : Expr → Array Expr → Array Expr
| app f a, as => getAppRevArgsAux f (as.push a)
| _,       as => as

@[inline] def getAppRevArgs (e : Expr) : Array Expr :=
getAppRevArgsAux e (Array.mkEmpty e.getAppNumArgs)

@[specialize] def withAppAux {α} (k : Expr → Array Expr → α) : Expr → Array Expr → Nat → α
| app f a, as, i => withAppAux f (as.set! i a) (i-1)
| f, as, i       => k f as

@[inline] def withApp {α} (e : Expr) (k : Expr → Array Expr → α) : α :=
let dummy := Expr.sort Level.zero;
let nargs := e.getAppNumArgs;
withAppAux k e (mkArray nargs dummy) (nargs-1)

@[specialize] private def withAppRevAux {α} (k : Expr → Array Expr → α) : Expr → Array Expr → α
| app f a, as => withAppRevAux f (as.push a)
| f,       as => k f as

@[inline] def withAppRev {α} (e : Expr) (k : Expr → Array Expr → α) : α :=
withAppRevAux k e (Array.mkEmpty e.getAppNumArgs)

def getRevArgD : Expr → Nat → Expr → Expr
| app f a, 0,   _ => a
| app f _, i+1, v => getRevArgD f i v
| _      , _,   v => v

def getRevArg! : Expr → Nat → Expr
| app f a, 0   => a
| app f _, i+1 => getRevArg! f i
| _      , _   => panic! "invalid index"

@[inline] def getArg! (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Expr :=
getRevArg! e (n - i - 1)

@[inline] def getArgD (e : Expr) (i : Nat) (v₀ : Expr) (n := e.getAppNumArgs) : Expr :=
getRevArgD e (n - i - 1) v₀

def isAppOf (e : Expr) (n : Name) : Bool :=
match e.getAppFn with
| const c _ => c == n
| _         => false

def isAppOfArity : Expr → Name → Nat → Bool
| const c _, n, 0   => c == n
| app f _,   n, a+1 => isAppOfArity f n a
| _,         _, _   => false

def appFn! : Expr → Expr
| app f _ => f
| _       => panic! "application expected"

def appArg! : Expr → Expr
| app _ a => a
| _       => panic! "application expected"

def constName! : Expr → Name
| const n _ => n
| _         => panic! "constant expected"

def constLevels! : Expr → List Level
| const _ ls => ls
| _          => panic! "constant expected"

def bvarIdx! : Expr → Nat
| bvar idx => idx
| _        => panic! "bvar expected"

def fvarId! : Expr → Name
| fvar n => n
| _      => panic! "fvar expected"

def bindingName! : Expr → Name
| forallE n _ _ _ => n
| lam n _ _ _     => n
| _               => panic! "binding expected"

def bindingDomain! : Expr → Expr
| forallE _ _ d _ => d
| lam _ _ d _     => d
| _               => panic! "binding expected"

def bindingBody! : Expr → Expr
| forallE _ _ _ b => b
| lam _ _ _ b     => b
| _               => panic! "binding expected"

def letName! : Expr → Name
| letE n _ _ _ => n
| _            => panic! "let expression expected"

/-- Instantiate the loose bound variables in `e` using `subst`.
    That is, a loose `Expr.bvar i` is replaced with `subst[i]`. -/
@[extern "lean_expr_instantiate"]
constant instantiate (e : @& Expr) (subst : @& Array Expr) : Expr := default _

@[extern "lean_expr_instantiate1"]
constant instantiate1 (e : @& Expr) (subst : @& Expr) : Expr := default _

/-- Similar to instantiate, but `Expr.bvar i` is replaced with `subst[subst.size - i - 1]` -/
@[extern "lean_expr_instantiate_rev"]
constant instantiateRev (e : @& Expr) (subst : @& Array Expr) : Expr := default _

/-- Similar to `instantiate`, but consider only the variables `xs` in the range `[beginIdx, endIdx)`.
    Function panics if `beginIdx <= endIdx <= xs.size` does not hold. -/
@[extern "lean_expr_instantiate_range"]
constant instantiateRange (e : @& Expr) (beginIdx endIdx : @& Nat) (xs : Array Expr) : Expr := default _

/-- Replace free variables `xs` with loose bound variables. -/
@[extern "lean_expr_abstract"]
constant abstract (e : @& Expr) (xs : @& Array Expr) : Expr := default _

/-- Similar to `abstract`, but consider only the first `min n xs.size` entries in `xs`. -/
@[extern "lean_expr_abstract_range"]
constant abstractRange (e : @& Expr) (n : @& Nat) (xs : @& Array Expr) : Expr := default _

@[extern "lean_instantiate_lparams"]
constant instantiateLevelParams (e : Expr) (paramNames : List Name) (lvls : List Level) : Expr := default _

instance : HasToString Expr :=
⟨Expr.dbgToString⟩

-- TODO: should not use dbgToString, but constructors.
instance : HasRepr Expr :=
⟨Expr.dbgToString⟩

end Expr

def mkConst (n : Name) (ls : List Level := []) : Expr :=
Expr.const n ls

def mkBinApp (f a b : Expr) :=
Expr.app (Expr.app f a) b

def mkBinCApp (f : Name) (a b : Expr) :=
mkBinApp (mkConst f) a b

def mkDecIsTrue (pred proof : Expr) :=
mkBinApp (Expr.const `Decidable.isTrue []) pred proof

def mkDecIsFalse (pred proof : Expr) :=
mkBinApp (Expr.const `Decidable.isFalse []) pred proof

abbrev ExprMap (α : Type)  := HashMap Expr α
abbrev PersistentExprMap (α : Type) := PHashMap Expr α
abbrev ExprSet := HashSet Expr
abbrev PersistentExprSet := PHashSet Expr
abbrev PExprSet := PersistentExprSet

/- Auxiliary type for forcing `==` to be structural equality for `Expr` -/
structure ExprStructEq :=
(val : Expr)

instance exprToExprStructEq : HasCoe Expr ExprStructEq := ⟨ExprStructEq.mk⟩

namespace ExprStructEq

protected def beq : ExprStructEq → ExprStructEq → Bool
| ⟨e₁⟩, ⟨e₂⟩ => Expr.equal e₁ e₂

protected def hash : ExprStructEq → USize
| ⟨e⟩ => e.hash

instance : Inhabited ExprStructEq := ⟨{ val := default _ }⟩
instance : HasBeq ExprStructEq := ⟨ExprStructEq.beq⟩
instance : Hashable ExprStructEq := ⟨ExprStructEq.hash⟩
instance : HasToString ExprStructEq := ⟨fun e => toString e.val⟩
instance : HasRepr ExprStructEq := ⟨fun e => repr e.val⟩

end ExprStructEq

abbrev ExprStructMap (α : Type) := HashMap ExprStructEq α
abbrev PersistentExprStructMap (α : Type) := PHashMap ExprStructEq α

namespace Expr

private partial def mkAppRevRangeAux (revArgs : Array Expr) (start : Nat) : Expr → Nat → Expr
| b, i =>
  if i == start then b
  else
    let i := i - 1;
    mkAppRevRangeAux (Expr.app b (revArgs.get! i)) i

/-- `mkAppRevRange f b e args == mkAppRev f (revArgs.extract b e)` -/
def mkAppRevRange (f : Expr) (beginIdx endIdx : Nat) (revArgs : Array Expr) : Expr :=
mkAppRevRangeAux revArgs beginIdx f endIdx

private def betaRevAux (revArgs : Array Expr) (sz : Nat) : Expr → Nat → Expr
| Expr.lam _ _ _ b, i =>
  if i + 1 < sz then
    betaRevAux b (i+1)
  else
    let n := sz - (i + 1);
    mkAppRevRange (b.instantiateRange n sz revArgs) 0 n revArgs
| b, i =>
  let n := sz - i;
  mkAppRevRange (b.instantiateRange n sz revArgs) 0 n revArgs

/-- If `f` is a lambda expression, than "beta-reduce" it using `revArgs`.
    This function is often used with `getAppRev` or `withAppRev`.
    Examples:
    - `betaRev (fun x y => t x y) #[]` ==> `fun x y => t x y`
    - `betaRev (fun x y => t x y) #[a]` ==> `fun y => t a y`
    - `betaRev (fun x y => t x y) #[a, b]` ==> t b a`
    - `betaRev (fun x y => t x y) #[a, b, c, d]` ==> t d c b a`
    Suppose `t` is `(fun x y => t x y) a b c d`, then
    `args := t.getAppRev` is `#[d, c, b, a]`,
    and `betaRev (fun x y => t x y) #[d, c, b, a]` is `t a b c d`. -/
def betaRev (f : Expr) (revArgs : Array Expr) : Expr :=
if revArgs.size == 0 then f
else betaRevAux revArgs revArgs.size f 0

/- The update functions here are defined using C code. They will try to avoid
   allocating new values using pointer equality.
   The hypotheses `(h : e.is... = true)` are used to ensure Lean will not crash
   at runtime.
   The `update*!` functions are inlined and provide a convenient way of using the
   update proofs without providing proofs.
   Note that if they are used under a match-expression, the compiler will eliminate
   the double-match. -/

@[extern "lean_expr_update_app"]
def updateApp (e : Expr) (newFn : Expr) (newArg : Expr) (h : e.isApp = true) : Expr :=
app newFn newArg

@[inline] def updateApp! (e : Expr) (newFn : Expr) (newArg : Expr) : Expr :=
match e with
| app fn arg => updateApp (app fn arg) newFn newArg rfl
| _          => panic! "application expected"

@[extern "lean_expr_update_const"]
def updateConst (e : Expr) (newLevels : List Level) (h : e.isConst = true) : Expr :=
const e.constName! newLevels

@[inline] def updateConst! (e : Expr) (newLevels : List Level) : Expr :=
match e with
| const n ls => updateConst (const n ls) newLevels rfl
| _          => panic! "constant expected"

@[extern "lean_expr_update_sort"]
def updateSort (e : Expr) (newLevel : Level) (h : e.isSort = true) : Expr :=
sort newLevel

@[inline] def updateSort! (e : Expr) (newLevel : Level) : Expr :=
match e with
| sort l => updateSort (sort l) newLevel rfl
| _      => panic! "level expected"

@[extern "lean_expr_update_proj"]
def updateProj (e : Expr) (newExpr : Expr) (h : e.isProj = true) : Expr :=
match e with
| proj s i _ => proj s i newExpr
| _          => e -- unreachable because of `h`

@[extern "lean_expr_update_mdata"]
def updateMData (e : Expr) (newExpr : Expr) (h : e.isMData = true) : Expr :=
match e with
| mdata d _ => mdata d newExpr
| _         => e -- unreachable because of `h`

@[inline] def updateMData! (e : Expr) (newExpr : Expr) : Expr :=
match e with
| mdata d e => updateMData (mdata d e) newExpr rfl
| _         => panic! "mdata expected"

@[inline] def updateProj! (e : Expr) (newExpr : Expr) : Expr :=
match e with
| proj s i e => updateProj (proj s i e) newExpr rfl
| _          => panic! "proj expected"

@[extern "lean_expr_update_forall"]
def updateForall (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) (h : e.isForall = true) : Expr :=
forallE e.bindingName! newBinfo newDomain newBody

@[inline] def updateForall! (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) : Expr :=
match e with
| forallE n bi d b => updateForall (forallE n bi d b) newBinfo newDomain newBody rfl
| _                => panic! "forall expected"

@[inline] def updateForallE! (e : Expr) (newDomain : Expr) (newBody : Expr) : Expr :=
match e with
| forallE n bi d b => updateForall (forallE n bi d b) bi newDomain newBody rfl
| _                => panic! "forall expected"

@[extern "lean_expr_update_lambda"]
def updateLambda (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) (h : e.isLambda = true) : Expr :=
lam e.bindingName! newBinfo newDomain newBody

@[inline] def updateLambda! (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) : Expr :=
match e with
| lam n bi d b => updateLambda (lam n bi d b) newBinfo newDomain newBody rfl
| _            => panic! "lambda expected"

@[inline] def updateLambdaE! (e : Expr) (newDomain : Expr) (newBody : Expr) : Expr :=
match e with
| lam n bi d b => updateLambda (lam n bi d b) bi newDomain newBody rfl
| _            => panic! "lambda expected"

@[extern "lean_expr_update_let"]
def updateLet (e : Expr) (newType : Expr) (newVal : Expr) (newBody : Expr) (h : e.isLet = true) : Expr :=
letE e.letName! newType newVal newBody

@[inline] def updateLet! (e : Expr) (newType : Expr) (newVal : Expr) (newBody : Expr) : Expr :=
match e with
| letE n t v b => updateLet (letE n t v b) newType newVal newBody rfl
| _            => panic! "let expression expected"

def updateFn : Expr → Expr → Expr
| app f a, g => app (updateFn f g) a
| _,       g => g

end Expr
end Lean
