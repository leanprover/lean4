/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.KVMap
import Lean.Level

namespace Lean

inductive Literal where
  | natVal (val : Nat)
  | strVal (val : String)
  deriving Inhabited, BEq, Repr

protected def Literal.hash : Literal → UInt64
  | Literal.natVal v => hash v
  | Literal.strVal v => hash v

instance : Hashable Literal := ⟨Literal.hash⟩

def Literal.lt : Literal → Literal → Bool
  | Literal.natVal _,  Literal.strVal _  => true
  | Literal.natVal v₁, Literal.natVal v₂ => v₁ < v₂
  | Literal.strVal v₁, Literal.strVal v₂ => v₁ < v₂
  | _,                 _                 => false

instance : LT Literal := ⟨fun a b => a.lt b⟩

instance (a b : Literal) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.lt b))

inductive BinderInfo where
  | default | implicit | strictImplicit | instImplicit | auxDecl
  deriving Inhabited, BEq, Repr

def BinderInfo.hash : BinderInfo → UInt64
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

instance : Hashable BinderInfo := ⟨BinderInfo.hash⟩

def BinderInfo.isInstImplicit : BinderInfo → Bool
  | BinderInfo.instImplicit => true
  | _                       => false

def BinderInfo.isImplicit : BinderInfo → Bool
  | BinderInfo.implicit => true
  | _                   => false

def BinderInfo.isStrictImplicit : BinderInfo → Bool
  | BinderInfo.strictImplicit => true
  | _                         => false

def BinderInfo.isAuxDecl : BinderInfo → Bool
  | BinderInfo.auxDecl => true
  | _                  => false

abbrev MData := KVMap
abbrev MData.empty : MData := {}

/--
 Cached hash code, cached results, and other data for `Expr`.
   hash           : 32-bits
   hasFVar        : 1-bit
   hasExprMVar    : 1-bit
   hasLevelMVar   : 1-bit
   hasLevelParam  : 1-bit
   nonDepLet      : 1-bit
   binderInfo     : 3-bits
   approxDepth    : 8-bits -- the approximate depth is used to minimize the number of hash collisions
   looseBVarRange : 16-bits -/
def Expr.Data := UInt64

instance: Inhabited Expr.Data :=
  inferInstanceAs (Inhabited UInt64)

def Expr.Data.hash (c : Expr.Data) : UInt64 :=
  c.toUInt32.toUInt64

instance : BEq Expr.Data where
  beq (a b : UInt64) := a == b

def Expr.Data.approxDepth (c : Expr.Data) : UInt8 :=
  ((c.shiftRight 40).land 255).toUInt8

def Expr.Data.looseBVarRange (c : Expr.Data) : UInt32 :=
  (c.shiftRight 48).toUInt32

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
  let bi := (c.shiftLeft 24).shiftRight 61
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
    (h : UInt64) (looseBVarRange : Nat) (approxDepth : UInt8)
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
      approxDepth.toUInt64.shiftLeft 40 +
      looseBVarRange.toUInt64.shiftLeft 48
    r

def Expr.mkData (h : UInt64) (looseBVarRange : Nat := 0) (approxDepth : UInt8 := 0) (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool := false) : Expr.Data :=
  Expr.mkDataCore h looseBVarRange approxDepth hasFVar hasExprMVar hasLevelMVar hasLevelParam false BinderInfo.default

def Expr.mkDataForBinder (h : UInt64) (looseBVarRange : Nat) (approxDepth : UInt8) (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool) (bi : BinderInfo) : Expr.Data :=
  Expr.mkDataCore h looseBVarRange approxDepth hasFVar hasExprMVar hasLevelMVar hasLevelParam false bi

def Expr.mkDataForLet (h : UInt64) (looseBVarRange : Nat) (approxDepth : UInt8) (hasFVar hasExprMVar hasLevelMVar hasLevelParam nonDepLet : Bool) : Expr.Data :=
  Expr.mkDataCore h looseBVarRange approxDepth hasFVar hasExprMVar hasLevelMVar hasLevelParam nonDepLet BinderInfo.default

open Expr

structure FVarId where
  name : Name
  deriving Inhabited, BEq, Hashable

instance : Repr FVarId where
  reprPrec n p := reprPrec n.name p

def FVarIdSet := Std.RBTree FVarId (Name.quickCmp ·.name ·.name)
  deriving Inhabited, EmptyCollection

instance : ForIn m FVarIdSet FVarId := inferInstanceAs (ForIn _ (Std.RBTree ..) ..)

def FVarIdHashSet := Std.HashSet FVarId
  deriving Inhabited, EmptyCollection

def FVarIdMap (α : Type) := Std.RBMap FVarId α (Name.quickCmp ·.name ·.name)

instance : EmptyCollection (FVarIdMap α) := inferInstanceAs (EmptyCollection (Std.RBMap ..))

instance : Inhabited (FVarIdMap α) where
  default := {}

/- We use the `E` suffix (short for `Expr`) to avoid collision with keywords.
   We considered using «...», but it is too inconvenient to use. -/
inductive Expr where
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
  deriving Inhabited

namespace Expr

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

def ctorName : Expr → String
  | bvar _ _        => "bvar"
  | fvar _ _        => "fvar"
  | mvar _ _        => "mvar"
  | sort _ _        => "sort"
  | const _ _ _     => "const"
  | app _ _ _       => "app"
  | lam _ _ _ _     => "lam"
  | forallE _ _ _ _ => "forallE"
  | letE _ _ _ _ _  => "letE"
  | lit _ _         => "lit"
  | mdata _ _ _     => "mdata"
  | proj _ _ _ _    => "proj"

protected def hash (e : Expr) : UInt64 :=
  e.data.hash

instance : Hashable Expr := ⟨Expr.hash⟩

def hasFVar (e : Expr) : Bool :=
  e.data.hasFVar

def hasExprMVar (e : Expr) : Bool :=
  e.data.hasExprMVar

def hasLevelMVar (e : Expr) : Bool :=
  e.data.hasLevelMVar

def hasMVar (e : Expr) : Bool :=
  let d := e.data
  d.hasExprMVar || d.hasLevelMVar

def hasLevelParam (e : Expr) : Bool :=
  e.data.hasLevelParam

def approxDepth (e : Expr) : UInt8 :=
  e.data.approxDepth

def looseBVarRange (e : Expr) : Nat :=
  e.data.looseBVarRange.toNat

def binderInfo (e : Expr) : BinderInfo :=
  e.data.binderInfo

@[export lean_expr_hash] def hashEx : Expr → UInt64 := hash
@[export lean_expr_has_fvar] def hasFVarEx : Expr → Bool := hasFVar
@[export lean_expr_has_expr_mvar] def hasExprMVarEx : Expr → Bool := hasExprMVar
@[export lean_expr_has_level_mvar] def hasLevelMVarEx : Expr → Bool := hasLevelMVar
@[export lean_expr_has_mvar] def hasMVarEx : Expr → Bool := hasMVar
@[export lean_expr_has_level_param] def hasLevelParamEx : Expr → Bool := hasLevelParam
@[export lean_expr_loose_bvar_range] def looseBVarRangeEx (e : Expr) : UInt32 := e.data.looseBVarRange
@[export lean_expr_binder_info] def binderInfoEx : Expr → BinderInfo := binderInfo

end Expr

def mkConst (n : Name) (lvls : List Level := []) : Expr :=
  Expr.const n lvls $ mkData (mixHash 5 $ mixHash (hash n) (hash lvls)) 0 0 false false (lvls.any Level.hasMVar) (lvls.any Level.hasParam)

def Literal.type : Literal → Expr
  | Literal.natVal _ => mkConst `Nat
  | Literal.strVal _ => mkConst `String

@[export lean_lit_type]
def Literal.typeEx : Literal → Expr := Literal.type

def mkBVar (idx : Nat) : Expr :=
  Expr.bvar idx $ mkData (mixHash 7 $ hash idx) (idx+1)

def mkSort (lvl : Level) : Expr :=
  Expr.sort lvl $ mkData (mixHash 11 $ hash lvl) 0 0 false false lvl.hasMVar lvl.hasParam

def mkFVar (fvarId : FVarId) : Expr :=
  Expr.fvar fvarId $ mkData (mixHash 13 $ hash fvarId) 0 0 true

def mkMVar (fvarId : MVarId) : Expr :=
  Expr.mvar fvarId $ mkData (mixHash 17 $ hash fvarId) 0 0 false true

def mkMData (m : MData) (e : Expr) : Expr :=
  let d := e.approxDepth+1
  Expr.mdata m e $ mkData (mixHash d.toUInt64 $ hash e) e.looseBVarRange d e.hasFVar e.hasExprMVar e.hasLevelMVar e.hasLevelParam

def mkProj (s : Name) (i : Nat) (e : Expr) : Expr :=
  let d := e.approxDepth+1
  Expr.proj s i e $ mkData (mixHash d.toUInt64 $ mixHash (hash s) $ mixHash (hash i) (hash e))
      e.looseBVarRange d e.hasFVar e.hasExprMVar e.hasLevelMVar e.hasLevelParam

def mkApp (f a : Expr) : Expr :=
  let d := (max f.approxDepth a.approxDepth) + 1
  Expr.app f a $ mkData (mixHash d.toUInt64 $ mixHash (hash f) (hash a))
    (max f.looseBVarRange a.looseBVarRange)
    d
    (f.hasFVar || a.hasFVar)
    (f.hasExprMVar || a.hasExprMVar)
    (f.hasLevelMVar || a.hasLevelMVar)
    (f.hasLevelParam || a.hasLevelParam)

def mkLambda (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : Expr :=
  let d := (max t.approxDepth b.approxDepth) + 1
  -- let x := x.eraseMacroScopes
  Expr.lam x t b $ mkDataForBinder (mixHash d.toUInt64 $ mixHash (hash t) (hash b))
    (max t.looseBVarRange (b.looseBVarRange - 1))
    d
    (t.hasFVar || b.hasFVar)
    (t.hasExprMVar || b.hasExprMVar)
    (t.hasLevelMVar || b.hasLevelMVar)
    (t.hasLevelParam || b.hasLevelParam)
    bi

def mkForall (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : Expr :=
  let d := (max t.approxDepth b.approxDepth) + 1
  -- let x := x.eraseMacroScopes
  Expr.forallE x t b $ mkDataForBinder (mixHash d.toUInt64 $ mixHash (hash t) (hash b))
    (max t.looseBVarRange (b.looseBVarRange - 1))
    d
    (t.hasFVar || b.hasFVar)
    (t.hasExprMVar || b.hasExprMVar)
    (t.hasLevelMVar || b.hasLevelMVar)
    (t.hasLevelParam || b.hasLevelParam)
    bi

/- Return `Unit -> type`. Do not confuse with `Thunk type` -/
def mkSimpleThunkType (type : Expr) : Expr :=
  mkForall Name.anonymous BinderInfo.default (Lean.mkConst `Unit) type

/- Return `fun (_ : Unit), e` -/
def mkSimpleThunk (type : Expr) : Expr :=
  mkLambda `_ BinderInfo.default (Lean.mkConst `Unit) type

def mkLet (x : Name) (t : Expr) (v : Expr) (b : Expr) (nonDep : Bool := false) : Expr :=
  let d := (max (max t.approxDepth v.approxDepth) b.approxDepth) + 1
  -- let x := x.eraseMacroScopes
  Expr.letE x t v b $ mkDataForLet (mixHash d.toUInt64 $ mixHash (hash t) $ mixHash (hash v) (hash b))
    (max (max t.looseBVarRange v.looseBVarRange) (b.looseBVarRange - 1))
    d
    (t.hasFVar || v.hasFVar || b.hasFVar)
    (t.hasExprMVar || v.hasExprMVar || b.hasExprMVar)
    (t.hasLevelMVar || v.hasLevelMVar || b.hasLevelMVar)
    (t.hasLevelParam || v.hasLevelParam || b.hasLevelParam)
    nonDep

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

def mkLit (l : Literal) : Expr :=
  Expr.lit l $ mkData (mixHash 3 (hash l))

def mkRawNatLit (n : Nat) : Expr :=
  mkLit (Literal.natVal n)

def mkNatLit (n : Nat) : Expr :=
  let r := mkRawNatLit n
  mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Nat) r (mkApp (mkConst ``instOfNatNat) r)

def mkStrLit (s : String) : Expr :=
  mkLit (Literal.strVal s)

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

def mkAppN (f : Expr) (args : Array Expr) : Expr :=
  args.foldl mkApp f

private partial def mkAppRangeAux (n : Nat) (args : Array Expr) (i : Nat) (e : Expr) : Expr :=
  if i < n then mkAppRangeAux n args (i+1) (mkApp e (args.get! i)) else e

/-- `mkAppRange f i j #[a_1, ..., a_i, ..., a_j, ... ]` ==> the expression `f a_i ... a_{j-1}` -/
def mkAppRange (f : Expr) (i j : Nat) (args : Array Expr) : Expr :=
  mkAppRangeAux j args i f

def mkAppRev (fn : Expr) (revArgs : Array Expr) : Expr :=
  revArgs.foldr (fun a r => mkApp r a) fn

namespace Expr
-- TODO: implement it in Lean
@[extern "lean_expr_dbg_to_string"]
constant dbgToString (e : @& Expr) : String

@[extern "lean_expr_quick_lt"]
constant quickLt (a : @& Expr) (b : @& Expr) : Bool

@[extern "lean_expr_lt"]
constant lt (a : @& Expr) (b : @& Expr) : Bool

/- Return true iff `a` and `b` are alpha equivalent.
   Binder annotations are ignored. -/
@[extern "lean_expr_eqv"]
constant eqv (a : @& Expr) (b : @& Expr) : Bool

instance : BEq Expr where
  beq := Expr.eqv

/- Return true iff `a` and `b` are equal.
   Binder names and annotations are taking into account. -/
@[extern "lean_expr_equal"]
constant equal (a : @& Expr) (b : @& Expr) : Bool

def isSort : Expr → Bool
  | sort _ _ => true
  | _        => false

def isProp : Expr → Bool
  | sort (Level.zero ..) _ => true
  | _ => false

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
  | app .. => true
  | _      => false

def isProj : Expr → Bool
  | proj ..  => true
  | _        => false

def isConst : Expr → Bool
  | const .. => true
  | _        => false

def isConstOf : Expr → Name → Bool
  | const n _ _, m => n == m
  | _,           _ => false

def isForall : Expr → Bool
  | forallE .. => true
  | _          => false

def isLambda : Expr → Bool
  | lam .. => true
  | _      => false

def isBinding : Expr → Bool
  | lam ..     => true
  | forallE .. => true
  | _          => false

def isLet : Expr → Bool
  | letE .. => true
  | _       => false

def isMData : Expr → Bool
  | mdata .. => true
  | _        => false

def isLit : Expr → Bool
  | lit .. => true
  | _      => false

def getForallBody : Expr → Expr
  | forallE _ _ b .. => getForallBody b
  | e                => e

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
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppArgsAux e (mkArray nargs dummy) (nargs-1)

private def getAppRevArgsAux : Expr → Array Expr → Array Expr
  | app f a _, as => getAppRevArgsAux f (as.push a)
  | _,         as => as

@[inline] def getAppRevArgs (e : Expr) : Array Expr :=
  getAppRevArgsAux e (Array.mkEmpty e.getAppNumArgs)

@[specialize] def withAppAux (k : Expr → Array Expr → α) : Expr → Array Expr → Nat → α
  | app f a _, as, i => withAppAux k f (as.set! i a) (i-1)
  | f,         as, i => k f as

@[inline] def withApp (e : Expr) (k : Expr → Array Expr → α) : α :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  withAppAux k e (mkArray nargs dummy) (nargs-1)

@[specialize] private def withAppRevAux (k : Expr → Array Expr → α) : Expr → Array Expr → α
  | app f a _, as => withAppRevAux k f (as.push a)
  | f,         as => k f as

@[inline] def withAppRev (e : Expr) (k : Expr → Array Expr → α) : α :=
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

def isNatLit : Expr → Bool
  | lit (Literal.natVal _) _ => true
  | _                        => false

def natLit? : Expr → Option Nat
  | lit (Literal.natVal v) _ => v
  | _                        => none

def isStringLit : Expr → Bool
  | lit (Literal.strVal _) _ => true
  | _                        => false

def isCharLit (e : Expr) : Bool :=
  e.isAppOfArity `Char.ofNat 1 && e.appArg!.isNatLit

def constName! : Expr → Name
  | const n _ _ => n
  | _           => panic! "constant expected"

def constName? : Expr → Option Name
  | const n _ _ => some n
  | _           => none

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
  | forallE _ d _ _ => d
  | lam _ d _ _     => d
  | _               => panic! "binding expected"

def bindingBody! : Expr → Expr
  | forallE _ _ b _ => b
  | lam _ _ b _     => b
  | _               => panic! "binding expected"

def bindingInfo! : Expr → BinderInfo
  | forallE _ _ _ c => c.binderInfo
  | lam _ _ _ c     => c.binderInfo
  | _               => panic! "binding expected"

def letName! : Expr → Name
  | letE n _ _ _ _ => n
  | _              => panic! "let expression expected"

def consumeMData : Expr → Expr
  | mdata _ e _ => consumeMData e
  | e           => e

def mdataExpr! : Expr → Expr
  | mdata _ e _ => e
  | _           => panic! "mdata expression expected"

def hasLooseBVars (e : Expr) : Bool :=
  e.looseBVarRange > 0

/- Remark: the following function assumes `e` does not have loose bound variables. -/
def isArrow (e : Expr) : Bool :=
  match e with
  | forallE _ _ b _ => !b.hasLooseBVars
  | _ => false

@[extern "lean_expr_has_loose_bvar"]
constant hasLooseBVar (e : @& Expr) (bvarIdx : @& Nat) : Bool

/-- Return true if `e` contains the loose bound variable `bvarIdx` in an explicit parameter, or in the range if `tryRange == true`. -/
def hasLooseBVarInExplicitDomain : Expr → Nat → Bool → Bool
  | Expr.forallE _ d b c, bvarIdx, tryRange => (c.binderInfo.isExplicit && hasLooseBVar d bvarIdx) || hasLooseBVarInExplicitDomain b (bvarIdx+1) tryRange
  | e, bvarIdx, tryRange                    => tryRange && hasLooseBVar e bvarIdx

/--
  Lower the loose bound variables `>= s` in `e` by `d`.
  That is, a loose bound variable `bvar i`.
  `i >= s` is mapped into `bvar (i-d)`.

  Remark: if `s < d`, then result is `e` -/
@[extern "lean_expr_lower_loose_bvars"]
constant lowerLooseBVars (e : @& Expr) (s d : @& Nat) : Expr

/--
  Lift loose bound variables `>= s` in `e` by `d`. -/
@[extern "lean_expr_lift_loose_bvars"]
constant liftLooseBVars (e : @& Expr) (s d : @& Nat) : Expr

/--
  `inferImplicit e numParams considerRange` updates the first `numParams` parameter binder annotations of the `e` forall type.
  It marks any parameter with an explicit binder annotation if there is another explicit arguments that depends on it or
  the resulting type if `considerRange == true`.

  Remark: we use this function to infer the bind annotations of inductive datatype constructors, and structure projections.
  When the `{}` annotation is used in these commands, we set `considerRange == false`.
-/
def inferImplicit : Expr → Nat → Bool → Expr
  | Expr.forallE n d b c, i+1, considerRange =>
    let b       := inferImplicit b i considerRange
    let newInfo := if c.binderInfo.isExplicit && hasLooseBVarInExplicitDomain b 0 considerRange then BinderInfo.implicit else c.binderInfo
    mkForall n newInfo d b
  | e, 0, _ => e
  | e, _, _ => e

/-- Instantiate the loose bound variables in `e` using `subst`.
    That is, a loose `Expr.bvar i` is replaced with `subst[i]`. -/
@[extern "lean_expr_instantiate"]
constant instantiate (e : @& Expr) (subst : @& Array Expr) : Expr

@[extern "lean_expr_instantiate1"]
constant instantiate1 (e : @& Expr) (subst : @& Expr) : Expr

/-- Similar to instantiate, but `Expr.bvar i` is replaced with `subst[subst.size - i - 1]` -/
@[extern "lean_expr_instantiate_rev"]
constant instantiateRev (e : @& Expr) (subst : @& Array Expr) : Expr

/-- Similar to `instantiate`, but consider only the variables `xs` in the range `[beginIdx, endIdx)`.
    Function panics if `beginIdx <= endIdx <= xs.size` does not hold. -/
@[extern "lean_expr_instantiate_range"]
constant instantiateRange (e : @& Expr) (beginIdx endIdx : @& Nat) (xs : @& Array Expr) : Expr

/-- Similar to `instantiateRev`, but consider only the variables `xs` in the range `[beginIdx, endIdx)`.
    Function panics if `beginIdx <= endIdx <= xs.size` does not hold. -/
@[extern "lean_expr_instantiate_rev_range"]
constant instantiateRevRange (e : @& Expr) (beginIdx endIdx : @& Nat) (xs : @& Array Expr) : Expr

/-- Replace free variables `xs` with loose bound variables. -/
@[extern "lean_expr_abstract"]
constant abstract (e : @& Expr) (xs : @& Array Expr) : Expr

/-- Similar to `abstract`, but consider only the first `min n xs.size` entries in `xs`. -/
@[extern "lean_expr_abstract_range"]
constant abstractRange (e : @& Expr) (n : @& Nat) (xs : @& Array Expr) : Expr

/-- Replace occurrences of the free variable `fvar` in `e` with `v` -/
def replaceFVar (e : Expr) (fvar : Expr) (v : Expr) : Expr :=
  (e.abstract #[fvar]).instantiate1 v

/-- Replace occurrences of the free variable `fvarId` in `e` with `v` -/
def replaceFVarId (e : Expr) (fvarId : FVarId) (v : Expr) : Expr :=
  replaceFVar e (mkFVar fvarId) v

/-- Replace occurrences of the free variables `fvars` in `e` with `vs` -/
def replaceFVars (e : Expr) (fvars : Array Expr) (vs : Array Expr) : Expr :=
  (e.abstract fvars).instantiateRev vs

instance : ToString Expr where
  toString := Expr.dbgToString

def isAtomic : Expr → Bool
  | Expr.const _ _ _ => true
  | Expr.sort _ _    => true
  | Expr.bvar _ _    => true
  | Expr.lit _ _     => true
  | Expr.mvar _ _    => true
  | Expr.fvar _ _    => true
  | _                => false

end Expr

def mkDecIsTrue (pred proof : Expr) :=
  mkAppB (mkConst `Decidable.isTrue) pred proof

def mkDecIsFalse (pred proof : Expr) :=
  mkAppB (mkConst `Decidable.isFalse) pred proof

open Std (HashMap HashSet PHashMap PHashSet)

abbrev ExprMap (α : Type)  := HashMap Expr α
abbrev PersistentExprMap (α : Type) := PHashMap Expr α
abbrev ExprSet := HashSet Expr
abbrev PersistentExprSet := PHashSet Expr
abbrev PExprSet := PersistentExprSet

/- Auxiliary type for forcing `==` to be structural equality for `Expr` -/
structure ExprStructEq where
  val : Expr
  deriving Inhabited

instance : Coe Expr ExprStructEq := ⟨ExprStructEq.mk⟩

namespace ExprStructEq

protected def beq : ExprStructEq → ExprStructEq → Bool
  | ⟨e₁⟩, ⟨e₂⟩ => Expr.equal e₁ e₂

protected def hash : ExprStructEq → UInt64
  | ⟨e⟩ => e.hash

instance : BEq ExprStructEq := ⟨ExprStructEq.beq⟩
instance : Hashable ExprStructEq := ⟨ExprStructEq.hash⟩
instance : ToString ExprStructEq := ⟨fun e => toString e.val⟩

end ExprStructEq

abbrev ExprStructMap (α : Type) := HashMap ExprStructEq α
abbrev PersistentExprStructMap (α : Type) := PHashMap ExprStructEq α

namespace Expr

private partial def mkAppRevRangeAux (revArgs : Array Expr) (start : Nat) (b : Expr) (i : Nat) : Expr :=
  if i == start then b
  else
    let i := i - 1
    mkAppRevRangeAux revArgs start (mkApp b (revArgs.get! i)) i

/-- `mkAppRevRange f b e args == mkAppRev f (revArgs.extract b e)` -/
def mkAppRevRange (f : Expr) (beginIdx endIdx : Nat) (revArgs : Array Expr) : Expr :=
  mkAppRevRangeAux revArgs beginIdx f endIdx

private def betaRevAux (revArgs : Array Expr) (sz : Nat) : Expr → Nat → Expr
  | Expr.lam _ _ b _, i =>
    if i + 1 < sz then
      betaRevAux revArgs sz b (i+1)
    else
      let n := sz - (i + 1)
      mkAppRevRange (b.instantiateRange n sz revArgs) 0 n revArgs
  | Expr.mdata _ b _, i => betaRevAux revArgs sz b i
  | b,                i =>
    let n := sz - i
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

def isHeadBetaTargetFn : Expr → Bool
  | Expr.lam _ _ _ _ => true
  | Expr.mdata _ b _ => isHeadBetaTargetFn b
  | _                => false

def headBeta (e : Expr) : Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn then betaRev f e.getAppRevArgs else e

def isHeadBetaTarget (e : Expr) : Bool :=
  e.getAppFn.isHeadBetaTargetFn

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

def getOptParamDefault? (e : Expr) : Option Expr :=
  if e.isAppOfArity `optParam 2 then
    some e.appArg!
  else
    none

def getAutoParamTactic? (e : Expr) : Option Expr :=
  if e.isAppOfArity `autoParam 2 then
    some e.appArg!
  else
    none

def isOptParam (e : Expr) : Bool :=
  e.isAppOfArity `optParam 2

def isAutoParam (e : Expr) : Bool :=
  e.isAppOfArity `autoParam 2

partial def consumeAutoOptParam (e : Expr) : Expr :=
  if e.isOptParam || e.isAutoParam then
    consumeAutoOptParam e.appFn!.appArg!
  else
    e

/-- Return true iff `e` contains a free variable which statisfies `p`. -/
@[inline] def hasAnyFVar (e : Expr) (p : FVarId → Bool) : Bool :=
  let rec @[specialize] visit (e : Expr) := if !e.hasFVar then false else
    match e with
    | Expr.forallE _ d b _   => visit d || visit b
    | Expr.lam _ d b _       => visit d || visit b
    | Expr.mdata _ e _       => visit e
    | Expr.letE _ t v b _    => visit t || visit v || visit b
    | Expr.app f a _         => visit f || visit a
    | Expr.proj _ _ e _      => visit e
    | e@(Expr.fvar fvarId _) => p fvarId
    | e                      => false
  visit e

def containsFVar (e : Expr) (fvarId : FVarId) : Bool :=
  e.hasAnyFVar (· == fvarId)

/- The update functions here are defined using C code. They will try to avoid
   allocating new values using pointer equality.
   The hypotheses `(h : e.is...)` are used to ensure Lean will not crash
   at runtime.
   The `update*!` functions are inlined and provide a convenient way of using the
   update proofs without providing proofs.
   Note that if they are used under a match-expression, the compiler will eliminate
   the double-match. -/

@[extern "lean_expr_update_app"]
def updateApp (e : Expr) (newFn : Expr) (newArg : Expr) (h : e.isApp) : Expr :=
  mkApp newFn newArg

@[inline] def updateApp! (e : Expr) (newFn : Expr) (newArg : Expr) : Expr :=
  match e with
  | app fn arg c => updateApp (app fn arg c) newFn newArg rfl
  | _            => panic! "application expected"

@[extern "lean_expr_update_const"]
def updateConst (e : Expr) (newLevels : List Level) (h : e.isConst) : Expr :=
  mkConst e.constName! newLevels

@[inline] def updateConst! (e : Expr) (newLevels : List Level) : Expr :=
  match e with
  | const n ls c => updateConst (const n ls c) newLevels rfl
  | _            => panic! "constant expected"

@[extern "lean_expr_update_sort"]
def updateSort (e : Expr) (newLevel : Level) (h : e.isSort) : Expr :=
  mkSort newLevel

@[inline] def updateSort! (e : Expr) (newLevel : Level) : Expr :=
  match e with
  | sort l c => updateSort (sort l c) newLevel rfl
  | _        => panic! "level expected"

@[extern "lean_expr_update_proj"]
def updateProj (e : Expr) (newExpr : Expr) (h : e.isProj) : Expr :=
  match e with
  | proj s i _ _ => mkProj s i newExpr
  | _            => e -- unreachable because of `h`

@[extern "lean_expr_update_mdata"]
def updateMData (e : Expr) (newExpr : Expr) (h : e.isMData) : Expr :=
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
def updateForall (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) (h : e.isForall) : Expr :=
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
def updateLambda (e : Expr) (newBinfo : BinderInfo) (newDomain : Expr) (newBody : Expr) (h : e.isLambda) : Expr :=
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
def updateLet (e : Expr) (newType : Expr) (newVal : Expr) (newBody : Expr) (h : e.isLet) : Expr :=
  mkLet e.letName! newType newVal newBody

@[inline] def updateLet! (e : Expr) (newType : Expr) (newVal : Expr) (newBody : Expr) : Expr :=
  match e with
  | letE n t v b c => updateLet (letE n t v b c) newType newVal newBody rfl
  | _              => panic! "let expression expected"

def updateFn : Expr → Expr → Expr
  | e@(app f a _), g => e.updateApp! (updateFn f g) a
  | _,             g => g

partial def eta (e : Expr) : Expr :=
  match e with
  | Expr.lam _ d b _ =>
    let b' := b.eta
    match b' with
    | Expr.app f (Expr.bvar 0 _) _ =>
      if !f.hasLooseBVar 0 then
        f.lowerLooseBVars 1 1
      else
        e.updateLambdaE! d b'
    | _ => e.updateLambdaE! d b'
  | _ => e

/- Instantiate level parameters -/

@[inline] def instantiateLevelParamsCore (s : Name → Option Level) (e : Expr) : Expr :=
  let rec @[specialize] visit (e : Expr) : Expr :=
    if !e.hasLevelParam then e
    else match e with
    | lam n d b _     => e.updateLambdaE! (visit d) (visit b)
    | forallE n d b _ => e.updateForallE! (visit d) (visit b)
    | letE n t v b _  => e.updateLet! (visit t) (visit v) (visit b)
    | app f a _       => e.updateApp! (visit f) (visit a)
    | proj _ _ s _    => e.updateProj! (visit s)
    | mdata _ b _     => e.updateMData! (visit b)
    | const _ us _    => e.updateConst! (us.map (fun u => u.instantiateParams s))
    | sort u _        => e.updateSort! (u.instantiateParams s)
    | e               => e
  visit e

private def getParamSubst : List Name → List Level → Name → Option Level
  | p::ps, u::us, p' => if p == p' then some u else getParamSubst ps us p'
  | _,     _,     _  => none

def instantiateLevelParams (e : Expr) (paramNames : List Name) (lvls : List Level) : Expr :=
  instantiateLevelParamsCore (getParamSubst paramNames lvls) e

private partial def getParamSubstArray (ps : Array Name) (us : Array Level) (p' : Name) (i : Nat) : Option Level :=
  if h : i < ps.size then
    let p := ps.get ⟨i, h⟩
    if h : i < us.size then
      let u := us.get ⟨i, h⟩
      if p == p' then some u else getParamSubstArray ps us p' (i+1)
    else none
  else none

def instantiateLevelParamsArray (e : Expr) (paramNames : Array Name) (lvls : Array Level) : Expr :=
  instantiateLevelParamsCore (fun p => getParamSubstArray paramNames lvls p 0) e

/- Annotate `e` with the given option. -/
def setOption (e : Expr) (optionName : Name) [KVMap.Value α] (val : α) : Expr :=
  mkMData (MData.empty.set optionName val) e

/- Annotate `e` with `pp.explicit := true`
   The delaborator uses `pp` options. -/
def setPPExplicit (e : Expr) (flag : Bool) :=
  e.setOption `pp.explicit flag

def setPPUniverses (e : Expr) (flag : Bool) :=
  e.setOption `pp.universes flag

/- If `e` is an application `f a_1 ... a_n` annotate `f`, `a_1` ... `a_n` with `pp.explicit := false`,
   and annotate `e` with `pp.explicit := true`. -/
def setAppPPExplicit (e : Expr) : Expr :=
  match e with
  | app .. =>
    let f    := e.getAppFn.setPPExplicit false
    let args := e.getAppArgs.map (·.setPPExplicit false)
    mkAppN f args |>.setPPExplicit true
  | _      => e

/- Similar for `setAppPPExplicit`, but only annotate children with `pp.explicit := false` if
   `e` does not contain metavariables. -/
def setAppPPExplicitForExposingMVars (e : Expr) : Expr :=
  match e with
  | app .. =>
    let f    := e.getAppFn.setPPExplicit false
    let args := e.getAppArgs.map fun arg => if arg.hasMVar then arg else arg.setPPExplicit false
    mkAppN f args |>.setPPExplicit true
  | _      => e

end Expr

def mkAnnotation (kind : Name) (e : Expr) : Expr :=
  mkMData (KVMap.empty.insert kind (DataValue.ofBool true)) e

def annotation? (kind : Name) (e : Expr) : Option Expr :=
  match e with
  | Expr.mdata d b _ => if d.size == 1 && d.getBool kind false then some b else none
  | _                => none

def mkLetFunAnnotation (e : Expr) : Expr :=
  mkAnnotation `let_fun e

def letFunAnnotation? (e : Expr) : Option Expr :=
  annotation? `let_fun e

def isLetFun (e : Expr) : Bool :=
  match letFunAnnotation? e with
  | none   => false
  | some e => e.isApp && e.appFn!.isLambda

/--
  Annotate `e` with the LHS annotation. The delaborator displays
  expressions of the form `lhs = rhs` as `lhs` when they have this annotation.
-/
def mkLHSGoal (e : Expr) : Expr :=
  mkAnnotation `_lhsGoal e

def isLHSGoal? (e : Expr) : Option Expr :=
  match annotation? `_lhsGoal e with
  | none => none
  | some e =>
    if e.isAppOfArity `Eq 3 then
      some e.appFn!.appArg!
    else
      none

def mkFreshFVarId {m : Type → Type} [Monad m] [MonadNameGenerator m] : m FVarId :=
  return { name := (← mkFreshId) }

def mkFreshMVarId {m : Type → Type} [Monad m] [MonadNameGenerator m] : m MVarId :=
  return { name := (← mkFreshId) }

def mkNot (p : Expr) : Expr := mkApp (mkConst ``Not) p
def mkOr (p q : Expr) : Expr := mkApp2 (mkConst ``Or) p q
def mkAnd (p q : Expr) : Expr := mkApp2 (mkConst ``And) p q
def mkEM (p : Expr) : Expr := mkApp (mkConst ``Classical.em) p

end Lean
