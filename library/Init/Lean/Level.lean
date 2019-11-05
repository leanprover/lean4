/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic
import Init.Data.HashMap
import Init.Data.PersistentHashMap
import Init.Lean.Name
import Init.Lean.Format

def Nat.imax (n m : Nat) : Nat :=
if m = 0 then 0 else Nat.max n m

namespace Lean

inductive Level
| zero   : Level
| succ   : Level → Level
| max    : Level → Level → Level
| imax   : Level → Level → Level
| param  : Name → Level
| mvar   : Name → Level

attribute [extern "lean_level_mk_succ"]  Level.succ
attribute [extern "lean_level_mk_max"]   Level.max
attribute [extern "lean_level_mk_imax"]  Level.imax
attribute [extern "lean_level_mk_param"] Level.param
attribute [extern "lean_level_mk_mvar"]  Level.mvar

namespace Level

instance : Inhabited Level := ⟨zero⟩

def isZero : Level → Bool
| zero => true
| _    => false

def isSucc : Level → Bool
| succ _ => true
| _      => false

def isMax : Level → Bool
| max _ _ => true
| _       => false

def isIMax : Level → Bool
| imax _ _ => true
| _        => false

def isMaxIMax : Level → Bool
| max _ _  => true
| imax _ _ => true
| _        => false

def isParam : Level → Bool
| param _ => true
| _       => false

def isMVar : Level → Bool
| mvar _ => true
| _      => false

def mvarId! : Level → Name
| mvar mvarId => mvarId
| _           => panic! "metavariable expected"

/-- If result is true, then forall assignments `A` which assigns all parameters and metavariables occuring
    in `l`, `l[A] != zero` -/
def isNeverZero : Level → Bool
| zero       => false
| param _    => false
| mvar _     => false
| succ _     => true
| max l₁ l₂  => isNeverZero l₁ || isNeverZero l₂
| imax l₁ l₂ => isNeverZero l₂

def one : Level := succ zero

@[extern "lean_level_has_param"]
def hasParam : Level → Bool
| param _    => true
| succ l     => hasParam l
| max l₁ l₂  => hasParam l₁ || hasParam l₂
| imax l₁ l₂ => hasParam l₁ || hasParam l₂
| _          => false

@[extern "lean_level_has_mvar"]
def hasMVar : Level → Bool
| mvar _     => true
| succ l     => hasMVar l
| max l₁ l₂  => hasMVar l₁ || hasMVar l₂
| imax l₁ l₂ => hasMVar l₁ || hasMVar l₂
| _          => false

def ofNat : Nat → Level
| 0   => zero
| n+1 => succ (ofNat n)

def addOffsetAux : Nat → Level → Level
| 0,     l => l
| (n+1), l => addOffsetAux n (Level.succ l)

def addOffset (l : Level) (n : Nat) : Level :=
l.addOffsetAux n

def isExplicit : Level → Bool
| zero   => true
| succ l => isExplicit l
| _      => false

def getOffsetAux : Level → Nat → Nat
| succ l, r => getOffsetAux l (r+1)
| l,      r => r

def getOffset (lvl : Level) : Nat :=
 getOffsetAux lvl 0

def getLevelOffset : Level → Level
| succ l => getLevelOffset l
| l      => l

def toNat (lvl : Level) : Option Nat :=
match lvl.getLevelOffset with
| zero => lvl.getOffset
| _    => none

def getDepth : Level → Nat
| succ l     => getDepth l + 1
| max l₁ l₂  => (Nat.max (getDepth l₁) (getDepth l₂)) + 1
| imax l₁ l₂ => (Nat.max (getDepth l₁) (getDepth l₂)) + 1
| _          => 0

def instantiate (s : Name → Option Level) : Level → Level
| zero        => zero
| succ l      => succ (instantiate l)
| max l₁ l₂   => max (instantiate l₁) (instantiate l₂)
| imax l₁ l₂  => imax (instantiate l₁) (instantiate l₂)
| l@(param n) =>
  match s n with
  | some l' => l'
  | none    => l
| l           => l

@[extern "lean_level_hash"]
protected constant hash (n : @& Level) : USize := arbitrary USize

instance hashable : Hashable Level := ⟨Level.hash⟩

@[extern "lean_level_eq"]
protected constant beq (a : @& Level) (b : @& Level) : Bool := arbitrary _

instance : HasBeq Level := ⟨Level.beq⟩

/-- `occurs u l` return `true` iff `u` occurs in `l`. -/
def occurs : Level → Level → Bool
| u, l@(succ l₁)     => u == l || occurs u l₁
| u, l@(max l₁ l₂)   => u == l || occurs u l₁ || occurs u l₂
| u, l@(imax l₁ l₂)  => u == l || occurs u l₁ || occurs u l₂
| u, l               => u == l

def ctorToNat : Level → Nat
| zero     => 0
| param _  => 1
| mvar _   => 2
| succ _   => 3
| max _ _  => 4
| imax _ _ => 5

/- TODO: use well founded recursion. -/
partial def normLtAux : Level → Nat → Level → Nat → Bool
| succ l₁, k₁, l₂, k₂ => normLtAux l₁ (k₁+1) l₂ k₂
| l₁, k₁, succ l₂, k₂ => normLtAux l₁ k₁ l₂ (k₂+1)
| l₁@(max l₁₁ l₁₂), k₁, l₂@(max l₂₁ l₂₂), k₂ =>
  if l₁ == l₂ then k₁ < k₂
  else if l₁₁ == l₂₁ then normLtAux l₁₁ 0 l₂₁ 0
  else normLtAux l₁₂ 0 l₂₂ 0
| l₁@(imax l₁₁ l₁₂), k₁, l₂@(imax l₂₁ l₂₂), k₂ =>
  if l₁ == l₂ then k₁ < k₂
  else if l₁₁ == l₂₁ then normLtAux l₁₁ 0 l₂₁ 0
  else normLtAux l₁₂ 0 l₂₂ 0
| param n₁, k₁, param n₂, k₂ => if n₁ == n₂ then k₁ < k₂ else Name.lt n₁ n₂     -- use Name.lt because it is lexicographical
| mvar n₁, k₁, mvar n₂, k₂ => if n₁ == n₂ then k₁ < k₂ else Name.quickLt n₁ n₂  -- metavariables are temporary, the actual order doesn't matter
| l₁, k₁, l₂, k₂ => if l₁ == l₂ then k₁ < k₂ else ctorToNat l₁ < ctorToNat l₂

/--
  A total order on level expressions that has the following properties
  - `succ l` is an immediate successor of `l`.
  - `zero` is the minimal element.
 This total order is used in the normalization procedure. -/
def normLt (l₁ l₂ : Level) : Bool :=
normLtAux l₁ 0 l₂ 0

private def isAlreadyNormalizedCheap : Level → Bool
| zero    => true
| param _ => true
| mvar _  => true
| succ l  => isAlreadyNormalizedCheap l
| _       => false

/- Auxiliary function used at `normalize` -/
private def mkIMaxAux : Level → Level → Level
| _,    zero => zero
| zero, l₂   => l₂
| l₁,   l₂   =>
  if l₁ == l₂ then l₁
  else imax l₁ l₂

/- Auxiliary function used at `normalize` -/
@[specialize] private partial def getMaxArgsAux (normalize : Level → Level) : Level → Bool → Array Level → Array Level
| max l₁ l₂, alreadyNormalized, lvls => getMaxArgsAux l₂ alreadyNormalized (getMaxArgsAux l₁ alreadyNormalized lvls)
| l,         false,             lvls => getMaxArgsAux (normalize l) true lvls
| l,         true,              lvls => lvls.push l


private def accMax (result : Level) (prev : Level) (offset : Nat) : Level :=
if result.isZero then prev.addOffset offset
else max result (prev.addOffset offset)

/- Auxiliary function used at `normalize`.
   Remarks:
   - `lvls` are sorted using `normLt`
   - `extraK` is the outter offset of the `max` term. We will push it inside.
   - `i` is the current array index
   - `prev + prevK` is the "previous" level that has not been added to `result` yet.
   - `result` is the accumulator
 -/
private partial def mkMaxAux (lvls : Array Level) (extraK : Nat) : Nat → Level → Nat → Level → Level
| i, prev, prevK, result =>
  if h : i < lvls.size then
    let lvl   := lvls.get ⟨i, h⟩;
    let curr  := lvl.getLevelOffset;
    let currK := lvl.getOffset;
    if curr == prev then
       mkMaxAux (i+1) curr currK result
    else
       mkMaxAux (i+1) curr currK (accMax result prev (extraK + prevK))
  else
    accMax result prev (extraK + prevK)

partial def normalize : Level → Level
| l =>
  if isAlreadyNormalizedCheap l then l
  else
    let k := l.getOffset;
    let u := l.getLevelOffset;
    match u with
    | max l₁ l₂  =>
      let lvls  := getMaxArgsAux normalize l₁ false #[];
      let lvls  := getMaxArgsAux normalize l₂ false lvls;
      let lvls  := lvls.qsort normLt;
      let lvl₁  := lvls.get! 0;
      let prev  := lvl₁.getLevelOffset;
      let prevK := lvl₁.getOffset;
      mkMaxAux lvls k 1 prev prevK zero
    | imax l₁ l₂ =>
      if l₂.isNeverZero then addOffset (normalize (max l₁ l₂)) k
      else
        let l₁ := normalize l₁;
        let l₂ := normalize l₂;
        addOffset (mkIMaxAux l₁ l₂) k
    | _ => unreachable!


/- Return true if `u` and `v` denote the same level.
   Check is currently incomplete. -/
def isEquiv (u v : Level) : Bool :=
u == v || u.normalize == v.normalize

/-- Reduce (if possible) universe level by 1 -/
def dec : Level → Option Level
| zero       => none
| param _    => none
| mvar _     => none
| succ l     => l
| max l₁ l₂  => max <$> dec l₁ <*> dec l₂
/- Remark: `max` in the following line is not a typo.
   If `dec l₂` succeeds, then `imax l₁ l₂` is equivalent to `max l₁ l₂`. -/
| imax l₁ l₂ => max <$> dec l₁ <*> dec l₂

/- Level to Format -/
namespace LevelToFormat
inductive Result
| leaf      : Format → Result
| num       : Nat → Result
| offset    : Result → Nat → Result
| maxNode   : List Result → Result
| imaxNode  : List Result → Result

def Result.succ : Result → Result
| Result.offset f k => Result.offset f (k+1)
| Result.num k      => Result.num (k+1)
| f                 => Result.offset f 1

def Result.max : Result → Result → Result
| f, Result.maxNode Fs => Result.maxNode (f::Fs)
| f₁, f₂               => Result.maxNode [f₁, f₂]

def Result.imax : Result → Result → Result
| f, Result.imaxNode Fs => Result.imaxNode (f::Fs)
| f₁, f₂                => Result.imaxNode [f₁, f₂]

def parenIfFalse : Format → Bool → Format
| f, true  => f
| f, false => f.paren

@[specialize] private def formatLst (fmt : Result → Format) : List Result → Format
| []    => Format.nil
| r::rs => Format.line ++ fmt r ++ formatLst rs

partial def Result.format : Result → Bool → Format
| Result.leaf f,         _ => f
| Result.num k,          _ => toString k
| Result.offset f 0,     r => Result.format f r
| Result.offset f (k+1), r =>
  let f' := Result.format f false;
  parenIfFalse (f' ++ "+" ++ fmt (k+1)) r
| Result.maxNode fs,    r => parenIfFalse (Format.group $ "max"  ++ formatLst (fun r => Result.format r false) fs) r
| Result.imaxNode fs,   r => parenIfFalse (Format.group $ "imax" ++ formatLst (fun r => Result.format r false) fs) r

def toResult : Level → Result
| zero       => Result.num 0
| succ l     => Result.succ (toResult l)
| max l₁ l₂  => Result.max (toResult l₁) (toResult l₂)
| imax l₁ l₂ => Result.imax (toResult l₁) (toResult l₂)
| param n    => Result.leaf (fmt n)
| mvar n     => Result.leaf (fmt n)

end LevelToFormat

protected def format (l : Level) : Format :=
(LevelToFormat.toResult l).format true

instance : HasFormat Level := ⟨Level.format⟩
instance : HasToString Level := ⟨Format.pretty ∘ Level.format⟩

/- The update functions here are defined using C code. They will try to avoid
   allocating new values using pointer equality.
   The hypotheses `(h : e.is... = true)` are used to ensure Lean will not crash
   at runtime.
   The `update*!` functions are inlined and provide a convenient way of using the
   update proofs without providing proofs.
   Note that if they are used under a match-expression, the compiler will eliminate
   the double-match. -/

@[extern "lean_level_update_succ"]
def updateSucc (lvl : Level) (newLvl : Level) (h : lvl.isSucc = true) : Level :=
succ newLvl

@[inline] def updateSucc! (lvl : Level) (newLvl : Level) : Level :=
match lvl with
| succ lvl => updateSucc (succ lvl) newLvl rfl
| _        => panic! "succ level expected"

@[extern "lean_level_update_max"]
def updateMax (lvl : Level) (newLhs : Level) (newRhs : Level) (h : lvl.isMax = true) : Level :=
max newLhs newRhs

@[inline] def updateMax! (lvl : Level) (newLhs : Level) (newRhs : Level) : Level :=
match lvl with
| max lhs rhs => updateMax (max lhs rhs) newLhs newRhs rfl
| _           => panic! "max level expected"

@[extern "lean_level_update_imax"]
def updateIMax (lvl : Level) (newLhs : Level) (newRhs : Level) (h : lvl.isIMax = true) : Level :=
imax newLhs newRhs

@[inline] def updateIMax! (lvl : Level) (newLhs : Level) (newRhs : Level) : Level :=
match lvl with
| max lhs rhs => updateIMax (imax lhs rhs) newLhs newRhs rfl
| _           => panic! "imax level expected"

end Level

abbrev LevelMap (α : Type)  := HashMap Level α
abbrev PersistentLevelMap (α : Type) := PHashMap Level α

end Lean
