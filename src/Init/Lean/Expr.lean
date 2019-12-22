/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.HashMap
import Init.Data.HashSet
import Init.Data.PersistentHashMap
import Init.Data.PersistentHashSet
import Init.Lean.Data.KVMap
import Init.Lean.Level

namespace Lean

inductive Literal
| natVal (val : Nat)
| strVal (val : String)

instance Literal.inhabited : Inhabited Literal := ⟨Literal.natVal 0⟩

def Literal.hash : Literal → USize
| Literal.natVal v => hash v
| Literal.strVal v => hash v

instance Literal.hashable : Hashable Literal := ⟨Literal.hash⟩

def Literal.beq : Literal → Literal → Bool
| Literal.natVal v₁, Literal.natVal v₂ => v₁ == v₂
| Literal.strVal v₁, Literal.strVal v₂ => v₁ == v₂
| _,                 _                 => false

instance Literal.hasBeq : HasBeq Literal := ⟨Literal.beq⟩

def Literal.lt : Literal → Literal → Bool
| Literal.natVal _,  Literal.strVal _  => true
| Literal.natVal v₁, Literal.natVal v₂ => v₁ < v₂
| Literal.strVal v₁, Literal.strVal v₂ => v₁ < v₂
| _,                 _                 => false

instance Literal.hasLess : HasLess Literal := ⟨fun a b => a.lt b⟩

inductive BinderInfo
| default | implicit | strictImplicit | instImplicit | auxDecl

def BinderInfo.hash : BinderInfo → USize
| BinderInfo.default        => 947
| BinderInfo.implicit       => 1019
| BinderInfo.strictImplicit => 1087
| BinderInfo.instImplicit   => 1153
| BinderInfo.auxDecl        => 1229

def BinderInfo.isExplicit : BinderInfo → Bool
| BinderInfo.implicit       => false
| BinderInfo.strictImplicit => false
| BinderInfo.instImplicit   => false
| _                         => true

instance BinderInfo.hashable : Hashable BinderInfo := ⟨BinderInfo.hash⟩

instance BinderInfo.inhabited : Inhabited BinderInfo := ⟨BinderInfo.default⟩

def BinderInfo.isInstImplicit : BinderInfo → Bool
| BinderInfo.instImplicit => true
| _                       => false

def BinderInfo.isAuxDecl : BinderInfo → Bool
| BinderInfo.auxDecl => true
| _                  => false

protected def BinderInfo.beq : BinderInfo → BinderInfo → Bool
| BinderInfo.default,        BinderInfo.default        => true
| BinderInfo.implicit,       BinderInfo.implicit       => true
| BinderInfo.strictImplicit, BinderInfo.strictImplicit => true
| BinderInfo.instImplicit,   BinderInfo.instImplicit   => true
| BinderInfo.auxDecl,        BinderInfo.auxDecl        => true
| _,                         _                         => false

instance BinderInfo.hasBeq : HasBeq BinderInfo := ⟨BinderInfo.beq⟩

abbrev MData := KVMap
abbrev MData.empty : MData := {KVMap .}
instance MVData.hasEmptc : HasEmptyc MData := ⟨MData.empty⟩

/--
 Cached hash code, cached results, and other data for `Expr`.
   hash           : 32-bits
   hasFVar        : 1-bit
   hasExprMVar    : 1-bit
   hasLevelMVar   : 1-bit
   hasLevelParam  : 1-bit
   nonDepLet      : 1-bit
   binderInfo     : 3-bits
   looseBVarRange : 24-bits -/
def Expr.Data := UInt64

instance Expr.Data.inhabited : Inhabited Expr.Data :=
inferInstanceAs (Inhabited UInt64)

def Expr.Data.hash (c : Expr.Data) : USize :=
c.toUInt32.toUSize

instance Expr.Data.hasBeq : HasBeq Expr.Data :=
⟨fun (a b : UInt64) => a == b⟩

def Expr.Data.looseBVarRange (c : Expr.Data) : UInt32 :=
(c.shiftRight 40).toUInt32

def Expr.Data.hasFVar (c : Expr.Data) : Bool :=
((c.shiftRight 32).land 1) == 1

def Expr.Data.hasExprMVar (c : Expr.Data) : Bool :=
((c.shiftRight 33).land 1) == 1

def Expr.Data.hasLevelMVar (c : Expr.Data) : Bool :=
((c.shiftRight 34).land 1) == 1

def Expr.Data.hasLevelParam (c : Expr.Data) : Bool :=
((c.shiftRight 35).land 1) == 1

def Expr.Data.nonDepLet (c : Expr.Data) : Bool :=
((c.shiftRight 36).land 1) == 1

@[extern c inline "(uint8_t)((#1 << 24) >> 61)"]
def Expr.Data.binderInfo (c : Expr.Data) : BinderInfo :=
let bi := (c.shiftLeft 24).shiftRight 61;
if bi == 0 then BinderInfo.default
else if bi == 1 then BinderInfo.implicit
else if bi == 2 then BinderInfo.strictImplicit
else if bi == 3 then BinderInfo.instImplicit
else BinderInfo.auxDecl

@[extern c inline "(uint64_t)#1"]
def BinderInfo.toUInt64 : BinderInfo → UInt64
| BinderInfo.default        => 0
| BinderInfo.implicit       => 1
| BinderInfo.strictImplicit => 2
| BinderInfo.instImplicit   => 3
| BinderInfo.auxDecl        => 4

@[inline] private def Expr.mkDataCore
    (h : USize) (looseBVarRange : Nat)
    (hasFVar hasExprMVar hasLevelMVar hasLevelParam nonDepLet : Bool) (bi : BinderInfo)
    : Expr.Data :=
if looseBVarRange > Nat.pow 2 24 - 1 then panic! "bound variable index is too big"
else
  let r : UInt64 :=
    h.toUInt32.toUInt64 +
    hasFVar.toUInt64.shiftLeft 32 +
    hasExprMVar.toUInt64.shiftLeft 33 +
    hasLevelMVar.toUInt64.shiftLeft 34 +
    hasLevelParam.toUInt64.shiftLeft 35 +
    nonDepLet.toUInt64.shiftLeft 36 +
    bi.toUInt64.shiftLeft 37 +
    looseBVarRange.toUInt64.shiftLeft 40;
  r

def Expr.mkData (h : USize) (looseBVarRange : Nat := 0) (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool := false) : Expr.Data :=
Expr.mkDataCore h looseBVarRange hasFVar hasExprMVar hasLevelMVar hasLevelParam false BinderInfo.default

def Expr.mkDataForBinder (h : USize) (looseBVarRange : Nat) (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool) (bi : BinderInfo) : Expr.Data :=
Expr.mkDataCore h looseBVarRange hasFVar hasExprMVar hasLevelMVar hasLevelParam false bi

def Expr.mkDataForLet (h : USize) (looseBVarRange : Nat) (hasFVar hasExprMVar hasLevelMVar hasLevelParam nonDepLet : Bool) : Expr.Data :=
Expr.mkDataCore h looseBVarRange hasFVar hasExprMVar hasLevelMVar hasLevelParam nonDepLet BinderInfo.default

open Expr

abbrev MVarId := Name
abbrev FVarId := Name

/- We use the `E` suffix (short for `Expr`) to avoid collision with keywords.
   We considered using «...», but it is too inconvenient to use. -/
inductive Expr
| bvar    : Nat → Data → Expr                       -- bound variables
| fvar    : FVarId → Data → Expr                    -- free variables
| mvar    : MVarId → Data → Expr                    -- meta variables
| sort    : Level → Data → Expr                     -- Sort
| const   : Name → List Level → Data → Expr         -- constants
| app     : Expr → Expr → Data → Expr               -- application
| lam     : Name → Expr → Expr → Data → Expr        -- lambda abstraction
| forallE : Name → Expr → Expr → Data → Expr        -- (dependent) arrow
| letE    : Name → Expr → Expr → Expr → Data → Expr -- let expressions
| lit     : Literal → Data → Expr                   -- literals
| mdata   : MData → Expr → Data → Expr              -- metadata
| proj    : Name → Nat → Expr → Data → Expr         -- projection
-- IMPORTANT: the following constructor will be deleted
| localE  : Name → Name → Expr → Data → Expr        -- Lean2 legacy. TODO: delete

namespace Expr

instance : Inhabited Expr :=
⟨sort (arbitrary _) (arbitrary _)⟩

@[inline] def data : Expr → Data
| bvar _ d        => d
| fvar _ d        => d
| mvar _ d        => d
| sort _ d        => d
| const _ _ d     => d
| app _ _ d       => d
| lam _ _ _ d     => d
| forallE _ _ _ d => d
| letE _ _ _ _ d  => d
| lit _ d         => d
| mdata _ _ d     => d
| proj _ _ _ d    => d
| localE _ _ _ d  => d

def hash (e : Expr) : USize :=
e.data.hash

instance : Hashable Expr := ⟨Expr.hash⟩

def hasFVar (e : Expr) : Bool :=
e.data.hasFVar

def hasExprMVar (e : Expr) : Bool :=
e.data.hasExprMVar

def hasLevelMVar (e : Expr) : Bool :=
e.data.hasLevelMVar

def hasMVar (e : Expr) : Bool :=
let d := e.data;
d.hasExprMVar || d.hasLevelMVar

def hasLevelParam (e : Expr) : Bool :=
e.data.hasLevelParam

def looseBVarRange (e : Expr) : Nat :=
e.data.looseBVarRange.toNat

def binderInfo (e : Expr) : BinderInfo :=
e.data.binderInfo

@[export lean_expr_hash] def hashEx : Expr → USize := hash
@[export lean_expr_has_fvar] def hasFVarEx : Expr → Bool := hasFVar
@[export lean_expr_has_expr_mvar] def hasExprMVarEx : Expr → Bool := hasExprMVar
@[export lean_expr_has_level_mvar] def hasLevelMVarEx : Expr → Bool := hasLevelMVar
@[export lean_expr_has_mvar] def hasMVarEx : Expr → Bool := hasMVar
@[export lean_expr_has_level_param] def hasLevelParamEx : Expr → Bool := hasLevelParam
@[export lean_expr_loose_bvar_range] def looseBVarRangeEx (e : Expr) : UInt32 := e.data.looseBVarRange
@[export lean_expr_binder_info] def binderInfoEx : Expr → BinderInfo := binderInfo

end Expr

def mkLit (l : Literal) : Expr :=
Expr.lit l $ mkData (mixHash 3 (hash l))

def mkNatLit (n : Nat) : Expr :=
mkLit (Literal.natVal n)

def mkStrLit (s : String) : Expr :=
mkLit (Literal.strVal s)

def mkConst (n : Name) (lvls : List Level := []) : Expr :=
Expr.const n lvls $ mkData (mixHash 5 $ mixHash (hash n) (hash lvls)) 0 false false (lvls.any Level.hasMVar) (lvls.any Level.hasParam)

def Literal.type : Literal → Expr
| Literal.natVal _ => mkConst `Nat
| Literal.strVal _ => mkConst `String

@[export lean_lit_type]
def Literal.typeEx : Literal → Expr := Literal.type

def mkBVar (idx : Nat) : Expr :=
Expr.bvar idx $ mkData (mixHash 7 $ hash idx) (idx+1)

def mkSort (lvl : Level) : Expr :=
Expr.sort lvl $ mkData (mixHash 11 $ hash lvl) 0 false false lvl.hasMVar lvl.hasParam

def mkFVar (fvarId : FVarId) : Expr :=
Expr.fvar fvarId $ mkData (mixHash 13 $ hash fvarId) 0 true

def mkMVar (fvarId : MVarId) : Expr :=
Expr.mvar fvarId $ mkData (mixHash 17 $ hash fvarId) 0 false true

def mkMData (d : MData) (e : Expr) : Expr :=
Expr.mdata d e $ mkData (mixHash 19 $ hash e) e.looseBVarRange e.hasFVar e.hasExprMVar e.hasLevelMVar e.hasLevelParam

def mkProj (s : Name) (i : Nat) (e : Expr) : Expr :=
Expr.proj s i e $ mkData (mixHash 23 $ mixHash (hash s) $ mixHash (hash i) (hash e))
    e.looseBVarRange e.hasFVar e.hasExprMVar e.hasLevelMVar e.hasLevelParam

def mkApp (f a : Expr) : Expr :=
Expr.app f a $ mkData (mixHash 29 $ mixHash (hash f) (hash a))
  (Nat.max f.looseBVarRange a.looseBVarRange)
  (f.hasFVar || a.hasFVar)
  (f.hasExprMVar || a.hasExprMVar)
  (f.hasLevelMVar || a.hasLevelMVar)
  (f.hasLevelParam || a.hasLevelParam)

def mkLambda (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : Expr :=
Expr.lam x t b $ mkDataForBinder (mixHash 31 $ mixHash (hash t) (hash b))
  (Nat.max t.looseBVarRange (b.looseBVarRange - 1))
  (t.hasFVar || b.hasFVar)
  (t.hasExprMVar || b.hasExprMVar)
  (t.hasLevelMVar || b.hasLevelMVar)
  (t.hasLevelParam || b.hasLevelParam)
  bi

def mkForall (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : Expr :=
Expr.forallE x t b $ mkDataForBinder (mixHash 37 $ mixHash (hash t) (hash b))
  (Nat.max t.looseBVarRange (b.looseBVarRange - 1))
  (t.hasFVar || b.hasFVar)
  (t.hasExprMVar || b.hasExprMVar)
  (t.hasLevelMVar || b.hasLevelMVar)
  (t.hasLevelParam || b.hasLevelParam)
  bi

def mkLet (x : Name) (t : Expr) (v : Expr) (b : Expr) (nonDep : Bool := false) : Expr :=
Expr.letE x t v b $ mkDataForLet (mixHash 41 $ mixHash (hash t) $ mixHash (hash v) (hash b))
  (Nat.max (Nat.max t.looseBVarRange v.looseBVarRange) (b.looseBVarRange - 1))
  (t.hasFVar || v.hasFVar || b.hasFVar)
  (t.hasExprMVar || v.hasExprMVar || b.hasExprMVar)
  (t.hasLevelMVar || v.hasLevelMVar || b.hasLevelMVar)
  (t.hasLevelParam || v.hasLevelParam || b.hasLevelParam)
  nonDep

-- TODO: delete
def mkLocal (x u : Name) (t : Expr) (bi : BinderInfo) : Expr :=
Expr.localE x u t $ mkDataForBinder (mixHash 43 $ hash t) t.looseBVarRange true t.hasExprMVar t.hasLevelMVar t.hasLevelParam bi

@[export lean_expr_mk_bvar] def mkBVarEx : Nat → Expr := mkBVar
@[export lean_expr_mk_fvar] def mkFVarEx : FVarId → Expr := mkFVar
@[export lean_expr_mk_mvar] def mkMVarEx : MVarId → Expr := mkMVar
@[export lean_expr_mk_sort] def mkSortEx : Level → Expr := mkSort
@[export lean_expr_mk_const] def mkConstEx (c : Name) (lvls : List Level) : Expr := mkConst c lvls
@[export lean_expr_mk_app] def mkAppEx : Expr → Expr → Expr := mkApp
@[export lean_expr_mk_lambda] def mkLambdaEx (n : Name) (d b : Expr) (bi : BinderInfo) : Expr := mkLambda n bi d b
@[export lean_expr_mk_forall] def mkForallEx (n : Name) (d b : Expr) (bi : BinderInfo) : Expr := mkForall n bi d b
@[export lean_expr_mk_let] def mkLetEx (n : Name) (t v b : Expr) : Expr := mkLet n t v b
@[export lean_expr_mk_lit] def mkLitEx : Literal → Expr := mkLit
@[export lean_expr_mk_mdata] def mkMDataEx : MData → Expr → Expr := mkMData
@[export lean_expr_mk_proj] def mkProjEx : Name → Nat → Expr → Expr := mkProj
@[export lean_expr_mk_local] def mkLocalEx : Name → Name → Expr → BinderInfo → Expr := mkLocal

def mkAppN (f : Expr) (args : Array Expr) : Expr :=
args.foldl mkApp f

private partial def mkAppRangeAux (n : Nat) (args : Array Expr) : Nat → Expr → Expr
| i, e => if i < n then mkAppRangeAux (i+1) (mkApp e (args.get! i)) else e

/-- `mkAppRange f i j #[a_1, ..., a_i, ..., a_j, ... ]` ==> the expression `f a_i ... a_{j-1}` -/
def mkAppRange (f : Expr) (i j : Nat) (args : Array Expr) : Expr :=
mkAppRangeAux j args i f

def mkAppRev (fn : Expr) (revArgs : Array Expr) : Expr :=
revArgs.foldr (fun a r => mkApp r a) fn

namespace Expr
-- TODO: implement it in Lean
@[extern "lean_expr_dbg_to_string"]
constant dbgToString (e : @& Expr) : String := arbitrary String

@[extern "lean_expr_quick_lt"]
constant quickLt (a : @& Expr) (b : @& Expr) : Bool := arbitrary _

@[extern "lean_expr_lt"]
constant lt (a : @& Expr) (b : @& Expr) : Bool := arbitrary _

/- Return true iff `a` and `b` are alpha equivalent.
   Binder annotations are ignored. -/
@[extern "lean_expr_eqv"]
constant eqv (a : @& Expr) (b : @& Expr) : Bool := arbitrary _

instance : HasBeq Expr := ⟨Expr.eqv⟩

/- Return true iff `a` and `b` are equal.
   Binder names and annotations are taking into account. -/
@[extern "lean_expr_equal"]
constant equal (a : @& Expr) (b : @& Expr) : Bool := arbitrary _

def isSort : Expr → Bool
| sort _ _ => true
| _        => false

def isBVar : Expr → Bool
| bvar _ _ => true
| _        => false

def isMVar : Expr → Bool
| mvar _ _ => true
| _        => false

def isFVar : Expr → Bool
| fvar _ _ => true
| _        => false

def isApp : Expr → Bool
| app _ _ _ => true
| _         => false

def isProj : Expr → Bool
| proj _ _ _ _ => true
| _            => false

def isConst : Expr → Bool
| const _ _ _ => true
| _           => false

def isConstOf : Expr → Name → Bool
| const n _ _, m => n == m
| _,           _ => false

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
| letE _ _ _ _ _ => true
| _              => false

def isMData : Expr → Bool
| mdata _ _ _ => true
| _           => false

def getAppFn : Expr → Expr
| app f a _ => getAppFn f
| e         => e

def getAppNumArgsAux : Expr → Nat → Nat
| app f a _, n => getAppNumArgsAux f (n+1)
| e,         n => n

def getAppNumArgs (e : Expr) : Nat :=
getAppNumArgsAux e 0

private def getAppArgsAux : Expr → Array Expr → Nat → Array Expr
| app f a _, as, i => getAppArgsAux f (as.set! i a) (i-1)
| _,         as, _ => as

@[inline] def getAppArgs (e : Expr) : Array Expr :=
let dummy := mkSort levelZero;
let nargs := e.getAppNumArgs;
getAppArgsAux e (mkArray nargs dummy) (nargs-1)

private def getAppRevArgsAux : Expr → Array Expr → Array Expr
| app f a _, as => getAppRevArgsAux f (as.push a)
| _,         as => as

@[inline] def getAppRevArgs (e : Expr) : Array Expr :=
getAppRevArgsAux e (Array.mkEmpty e.getAppNumArgs)

@[specialize] def withAppAux {α} (k : Expr → Array Expr → α) : Expr → Array Expr → Nat → α
| app f a _, as, i => withAppAux f (as.set! i a) (i-1)
| f,         as, i => k f as

@[inline] def withApp {α} (e : Expr) (k : Expr → Array Expr → α) : α :=
let dummy := mkSort levelZero;
let nargs := e.getAppNumArgs;
withAppAux k e (mkArray nargs dummy) (nargs-1)

@[specialize] private def withAppRevAux {α} (k : Expr → Array Expr → α) : Expr → Array Expr → α
| app f a _, as => withAppRevAux f (as.push a)
| f,         as => k f as

@[inline] def withAppRev {α} (e : Expr) (k : Expr → Array Expr → α) : α :=
withAppRevAux k e (Array.mkEmpty e.getAppNumArgs)

def getRevArgD : Expr → Nat → Expr → Expr
| app f a _, 0,   _ => a
| app f _ _, i+1, v => getRevArgD f i v
| _,         _,   v => v

def getRevArg! : Expr → Nat → Expr
| app f a _, 0   => a
| app f _ _, i+1 => getRevArg! f i
| _,         _   => panic! "invalid index"

@[inline] def getArg! (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Expr :=
getRevArg! e (n - i - 1)

@[inline] def getArgD (e : Expr) (i : Nat) (v₀ : Expr) (n := e.getAppNumArgs) : Expr :=
getRevArgD e (n - i - 1) v₀

def isAppOf (e : Expr) (n : Name) : Bool :=
match e.getAppFn with
| const c _ _ => c == n
| _           => false

def isAppOfArity : Expr → Name → Nat → Bool
| const c _ _, n, 0   => c == n
| app f _ _,   n, a+1 => isAppOfArity f n a
| _,           _, _   => false

def appFn! : Expr → Expr
| app f _ _ => f
| _         => panic! "application expected"

def appArg! : Expr → Expr
| app _ a _ => a
| _         => panic! "application expected"

def constName! : Expr → Name
| const n _ _ => n
| _           => panic! "constant expected"

def constLevels! : Expr → List Level
| const _ ls _ => ls
| _            => panic! "constant expected"

def bvarIdx! : Expr → Nat
| bvar idx _ => idx
| _          => panic! "bvar expected"

def fvarId! : Expr → FVarId
| fvar n _ => n
| _        => panic! "fvar expected"

def mvarId! : Expr → MVarId
| mvar n _ => n
| _        => panic! "mvar expected"

def bindingName! : Expr → Name
| forallE n _ _ _ => n
| lam n _ _ _     => n
| _               => panic! "binding expected"

def bindingDomain! : Expr → Expr
| forallE _ _ d _ => d
| lam _ _ d _     => d
| _               => panic! "binding expected"

def bindingBody! : Expr → Expr
| forallE _ _ b _ => b
| lam _ _ b _     => b
| _               => panic! "binding expected"

def letName! : Expr → Name
| letE n _ _ _ _ => n
| _              => panic! "let expression expected"

def hasLooseBVars (e : Expr) : Bool :=
e.looseBVarRange > 0

@[extern "lean_expr_has_loose_bvar"]
constant hasLooseBVar (e : @& Expr) (bvarIdx : @& Nat) : Bool := arbitrary _

/-- Instantiate the loose bound variables in `e` using `subst`.
    That is, a loose `Expr.bvar i` is replaced with `subst[i]`. -/
@[extern "lean_expr_instantiate"]
constant instantiate (e : @& Expr) (subst : @& Array Expr) : Expr := arbitrary _

@[extern "lean_expr_instantiate1"]
constant instantiate1 (e : @& Expr) (subst : @& Expr) : Expr := arbitrary _

/-- Similar to instantiate, but `Expr.bvar i` is replaced with `subst[subst.size - i - 1]` -/
@[extern "lean_expr_instantiate_rev"]
constant instantiateRev (e : @& Expr) (subst : @& Array Expr) : Expr := arbitrary _

/-- Similar to `instantiate`, but consider only the variables `xs` in the range `[beginIdx, endIdx)`.
    Function panics if `beginIdx <= endIdx <= xs.size` does not hold. -/
@[extern "lean_expr_instantiate_range"]
constant instantiateRange (e : @& Expr) (beginIdx endIdx : @& Nat) (xs : @& Array Expr) : Expr := arbitrary _

/-- Similar to `instantiateRev`, but consider only the variables `xs` in the range `[beginIdx, endIdx)`.
    Function panics if `beginIdx <= endIdx <= xs.size` does not hold. -/
@[extern "lean_expr_instantiate_rev_range"]
constant instantiateRevRange (e : @& Expr) (beginIdx endIdx : @& Nat) (xs : @& Array Expr) : Expr := arbitrary _

/-- Replace free variables `xs` with loose bound variables. -/
@[extern "lean_expr_abstract"]
constant abstract (e : @& Expr) (xs : @& Array Expr) : Expr := arbitrary _

/-- Similar to `abstract`, but consider only the first `min n xs.size` entries in `xs`. -/
@[extern "lean_expr_abstract_range"]
constant abstractRange (e : @& Expr) (n : @& Nat) (xs : @& Array Expr) : Expr := arbitrary _

instance : HasToString Expr :=
⟨Expr.dbgToString⟩

-- TODO: should not use dbgToString, but constructors.
instance : HasRepr Expr :=
⟨Expr.dbgToString⟩

end Expr

def mkAppB (f a b : Expr) := mkApp (mkApp f a) b
def mkApp2 (f a b : Expr) := mkAppB f a b
def mkApp3 (f a b c : Expr) := mkApp (mkAppB f a b) c
def mkApp4 (f a b c d : Expr) := mkAppB (mkAppB f a b) c d
def mkApp5 (f a b c d e : Expr) := mkApp (mkApp4 f a b c d) e
def mkApp6 (f a b c d e₁ e₂ : Expr) := mkAppB (mkApp4 f a b c d) e₁ e₂
def mkApp7 (f a b c d e₁ e₂ e₃ : Expr) := mkApp3 (mkApp4 f a b c d) e₁ e₂ e₃
def mkApp8 (f a b c d e₁ e₂ e₃ e₄ : Expr) := mkApp4 (mkApp4 f a b c d) e₁ e₂ e₃ e₄
def mkApp9 (f a b c d e₁ e₂ e₃ e₄ e₅ : Expr) := mkApp5 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅
def mkApp10 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ : Expr) := mkApp6 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅ e₆

def mkDecIsTrue (pred proof : Expr) :=
mkAppB (mkConst `Decidable.isTrue) pred proof

def mkDecIsFalse (pred proof : Expr) :=
mkAppB (mkConst `Decidable.isFalse) pred proof

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

instance : Inhabited ExprStructEq := ⟨{ val := arbitrary _ }⟩
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
    mkAppRevRangeAux (mkApp b (revArgs.get! i)) i

/-- `mkAppRevRange f b e args == mkAppRev f (revArgs.extract b e)` -/
def mkAppRevRange (f : Expr) (beginIdx endIdx : Nat) (revArgs : Array Expr) : Expr :=
mkAppRevRangeAux revArgs beginIdx f endIdx

private def betaRevAux (revArgs : Array Expr) (sz : Nat) : Expr → Nat → Expr
| Expr.lam _ _ b _, i =>
  if i + 1 < sz then
    betaRevAux b (i+1)
  else
    let n := sz - (i + 1);
    mkAppRevRange (b.instantiateRange n sz revArgs) 0 n revArgs
| Expr.mdata _ b _, i => betaRevAux b i
| b,                i =>
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

def isHeadBetaTarget : Expr → Bool
| Expr.lam _ _ _ _ => true
| Expr.mdata _ b _ => isHeadBetaTarget b
| _                => false

def headBeta (e : Expr) : Expr :=
let f := e.getAppFn;
if f.isHeadBetaTarget then betaRev f e.getAppRevArgs else e

private def etaExpandedBody : Expr → Nat → Nat → Option Expr
| app f (bvar j _) _, n+1, i => if j == i then etaExpandedBody f n (i+1) else none
| _,                  n+1, _ => none
| f,                  0,   _ => if f.hasLooseBVars then none else some f

private def etaExpandedAux : Expr → Nat → Option Expr
| lam _ _ b _, n => etaExpandedAux b (n+1)
| e,           n => etaExpandedBody e n 0

/--
  If `e` is of the form `(fun x₁ ... xₙ => f x₁ ... xₙ)` and `f` does not contain `x₁`, ..., `xₙ`,
  then return `some f`. Otherwise, return `none`.

  It assumes `e` does not have loose bound variables.

  Remark: `ₙ` may be 0 -/
def etaExpanded? (e : Expr) : Option Expr :=
etaExpandedAux e 0

/-- Similar to `etaExpanded?`, but only succeeds if `ₙ ≥ 1`. -/
def etaExpandedStrict? : Expr → Option Expr
| lam _ _ b _ => etaExpandedAux b 1
| _           => none

@[specialize] private partial def hasAnyFVarAux (p : FVarId → Bool) : Expr → Bool
| e => if !e.hasFVar then false else
  match e with
  | Expr.forallE _ d b _   => hasAnyFVarAux d || hasAnyFVarAux b
  | Expr.lam _ d b _       => hasAnyFVarAux d || hasAnyFVarAux b
  | Expr.mdata _ e _       => hasAnyFVarAux e
  | Expr.letE _ t v b _    => hasAnyFVarAux t || hasAnyFVarAux v || hasAnyFVarAux b
  | Expr.app f a _         => hasAnyFVarAux f || hasAnyFVarAux a
  | Expr.proj _ _ e _      => hasAnyFVarAux e
  | Expr.localE _ _ _ _    => unreachable!
  | e@(Expr.fvar fvarId _) => p fvarId
  | e                      => false

/-- Return true iff `e` contains a free variable which statisfies `p`. -/
@[inline] def hasAnyFVar (e : Expr) (p : FVarId → Bool) : Bool :=
hasAnyFVarAux p e

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
mkApp newFn newArg

@[inline] def updateApp! (e : Expr) (newFn : Expr) (newArg : Expr) : Expr :=
match e with
| app fn arg c => updateApp (app fn arg c) newFn newArg rfl
| _            => panic! "application expected"

@[extern "lean_expr_update_const"]
def updateConst (e : Expr) (newLevels : List Level) (h : e.isConst = true) : Expr :=
mkConst e.constName! newLevels

@[inline] def updateConst! (e : Expr) (newLevels : List Level) : Expr :=
match e with
| const n ls c => updateConst (const n ls c) newLevels rfl
| _            => panic! "constant expected"

@[extern "lean_expr_update_sort"]
def updateSort (e : Expr) (newLevel : Level) (h : e.isSort = true) : Expr :=
mkSort newLevel

@[inline] def updateSort! (e : Expr) (newLevel : Level) : Expr :=
match e with
| sort l c => updateSort (sort l c) newLevel rfl
| _        => panic! "level expected"

@[extern "lean_expr_update_proj"]
def updateProj (e : Expr) (newExpr : Expr) (h : e.isProj = true) : Expr :=
match e with
| proj s i _ _ => mkProj s i newExpr
| _            => e -- unreachable because of `h`

@[extern "lean_expr_update_mdata"]
def updateMData (e : Expr) (newExpr : Expr) (h : e.isMData = true) : Expr :=
match e with
| mdata d _ _ => mkMData d newExpr
| _           => e -- unreachable because of `h`

@[inline] def updateMData! (e : Expr) (newExpr : Expr) : Expr :=
match e with
| mdata d e c => updateMData (mdata d e c) newExpr rfl
| _           => panic! "mdata expected"

@[inline] def updateProj! (e : Expr) (newExpr : Expr) : Expr :=
match e with
| proj s i e c => updateProj (proj s i e c) newExpr rfl
| _            => panic! "proj expected"

@[extern "lean_expr_update_forall"]
def updateForall (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) (h : e.isForall = true) : Expr :=
mkForall e.bindingName! newBinfo newDomain newBody

@[inline] def updateForall! (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) : Expr :=
match e with
| forallE n d b c => updateForall (forallE n d b c) newBinfo newDomain newBody rfl
| _               => panic! "forall expected"

@[inline] def updateForallE! (e : Expr) (newDomain : Expr) (newBody : Expr) : Expr :=
match e with
| forallE n d b c => updateForall (forallE n d b c) c.binderInfo newDomain newBody rfl
| _               => panic! "forall expected"

@[extern "lean_expr_update_lambda"]
def updateLambda (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) (h : e.isLambda = true) : Expr :=
mkLambda e.bindingName! newBinfo newDomain newBody

@[inline] def updateLambda! (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) : Expr :=
match e with
| lam n d b c => updateLambda (lam n d b c) newBinfo newDomain newBody rfl
| _           => panic! "lambda expected"

@[inline] def updateLambdaE! (e : Expr) (newDomain : Expr) (newBody : Expr) : Expr :=
match e with
| lam n d b c => updateLambda (lam n d b c) c.binderInfo newDomain newBody rfl
| _           => panic! "lambda expected"

@[extern "lean_expr_update_let"]
def updateLet (e : Expr) (newType : Expr) (newVal : Expr) (newBody : Expr) (h : e.isLet = true) : Expr :=
mkLet e.letName! newType newVal newBody

@[inline] def updateLet! (e : Expr) (newType : Expr) (newVal : Expr) (newBody : Expr) : Expr :=
match e with
| letE n t v b c => updateLet (letE n t v b c) newType newVal newBody rfl
| _              => panic! "let expression expected"

def updateFn : Expr → Expr → Expr
| e@(app f a _), g => e.updateApp (updateFn f g) a rfl
| _,             g => g

/- Instantiate level parameters -/

namespace InstantiateLevelParams

@[inline] def visit (f : Expr → Expr) (e : Expr) : Expr :=
if e.hasLevelParam then f e else e

@[specialize] partial def instantiate (s : Name → Option Level) : Expr → Expr
| e@(lam n d b _)     => e.updateLambdaE! (visit instantiate d) (visit instantiate b)
| e@(forallE n d b _) => e.updateForallE! (visit instantiate d) (visit instantiate b)
| e@(letE n t v b _)  => e.updateLet! (visit instantiate t) (visit instantiate v) (visit instantiate b)
| e@(app f a _)       => e.updateApp (visit instantiate f) (visit instantiate a) rfl
| e@(proj _ _ s _)    => e.updateProj (visit instantiate s) rfl
| e@(mdata _ b _)     => e.updateMData (visit instantiate b) rfl
| e@(const _ us _)    => e.updateConst (us.map (fun u => u.instantiateParams s)) rfl
| e@(sort u _)        => e.updateSort (u.instantiateParams s) rfl
| localE _ _ _ _      => unreachable!
| e => e

end InstantiateLevelParams

@[inline] def instantiateLevelParamsCore (s : Name → Option Level) (e : Expr) : Expr :=
if e.hasLevelParam then InstantiateLevelParams.instantiate s e else e

private def getParamSubst : List Name → List Level → Name → Option Level
| p::ps, u::us, p' => if p == p' then some u else getParamSubst ps us p'
| _,     _,     _  => none

def instantiateLevelParams (e : Expr) (paramNames : List Name) (lvls : List Level) : Expr :=
instantiateLevelParamsCore (getParamSubst paramNames lvls) e

private partial def getParamSubstArray (ps : Array Name) (us : Array Level) (p' : Name) : Nat → Option Level
| i =>
  if h : i < ps.size then
    let p := ps.get ⟨i, h⟩;
    if h : i < us.size then
      let u := us.get ⟨i, h⟩;
      if p == p' then some u else getParamSubstArray (i+1)
    else none
  else none

def instantiateLevelParamsArray (e : Expr) (paramNames : Array Name) (lvls : Array Level) : Expr :=
instantiateLevelParamsCore (fun p => getParamSubstArray paramNames lvls p 0) e

end Expr
end Lean
