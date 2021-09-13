/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.PersistentHashMap
import Std.Data.PersistentHashSet
import Lean.Hygiene
import Lean.Data.Name
import Lean.Data.Format

def Nat.imax (n m : Nat) : Nat :=
  if m = 0 then 0 else Nat.max n m

namespace Lean

/--
 Cached hash code, cached results, and other data for `Level`.
   hash      : 32-bits
   hasMVar   : 1-bit
   hasParam  : 1-bit
   depth     : 24-bits -/
def Level.Data := UInt64

instance : Inhabited Level.Data :=
  inferInstanceAs (Inhabited UInt64)

def Level.Data.hash (c : Level.Data) : UInt64 :=
  c.toUInt32.toUInt64

instance : BEq Level.Data :=
  ⟨fun (a b : UInt64) => a == b⟩

def Level.Data.depth (c : Level.Data) : UInt32 :=
  (c.shiftRight 40).toUInt32

def Level.Data.hasMVar (c : Level.Data) : Bool :=
  ((c.shiftRight 32).land 1) == 1

def Level.Data.hasParam (c : Level.Data) : Bool :=
  ((c.shiftRight 33).land 1) == 1

def Level.mkData (h : UInt64) (depth : Nat) (hasMVar hasParam : Bool) : Level.Data :=
  if depth > Nat.pow 2 24 - 1 then panic! "universe level depth is too big"
  else
    let r : UInt64 := h.toUInt32.toUInt64 + hasMVar.toUInt64.shiftLeft 32 + hasParam.toUInt64.shiftLeft 33 + depth.toUInt64.shiftLeft 40
    r

open Level

structure MVarId where
  name : Name
  deriving Inhabited, BEq, Hashable

instance : Repr MVarId where
  reprPrec n p := reprPrec n.name p

def MVarIdSet := Std.RBTree MVarId (Name.quickCmp ·.name ·.name)
  deriving Inhabited, EmptyCollection

instance : ForIn m MVarIdSet MVarId := inferInstanceAs (ForIn _ (Std.RBTree ..) ..)

def MVarIdMap (α : Type) := Std.RBMap MVarId α (Name.quickCmp ·.name ·.name)

instance : EmptyCollection (MVarIdMap α) := inferInstanceAs (EmptyCollection (Std.RBMap ..))

instance : Inhabited (MVarIdMap α) where
  default := {}

inductive Level where
  | zero   : Data → Level
  | succ   : Level → Data → Level
  | max    : Level → Level → Data → Level
  | imax   : Level → Level → Data → Level
  | param  : Name → Data → Level
  | mvar   : MVarId → Data → Level
  deriving Inhabited

namespace Level

@[inline] def data : Level → Data
  | zero d     => d
  | mvar _ d   => d
  | param _ d  => d
  | succ _ d   => d
  | max _ _ d  => d
  | imax _ _ d => d

protected def hash (u : Level) : UInt64 :=
  u.data.hash

instance : Hashable Level := ⟨Level.hash⟩

def depth (u : Level) : Nat :=
  u.data.depth.toNat

def hasMVar (u : Level) : Bool :=
  u.data.hasMVar

def hasParam (u : Level) : Bool :=
  u.data.hasParam

@[export lean_level_hash] def hashEx (u : Level) : UInt32 := hash u |>.toUInt32
@[export lean_level_has_mvar] def hasMVarEx : Level → Bool := hasMVar
@[export lean_level_has_param] def hasParamEx : Level → Bool := hasParam
@[export lean_level_depth] def depthEx (u : Level) : UInt32 := u.data.depth

end Level

def levelZero :=
  Level.zero $ mkData 2221 0 false false

def mkLevelMVar (mvarId : MVarId) :=
  Level.mvar mvarId $ mkData (mixHash 2237 $ hash mvarId) 0 true false

def mkLevelParam (name : Name) :=
  Level.param name $ mkData (mixHash 2239 $ hash name) 0 false true

def mkLevelSucc (u : Level) :=
  Level.succ u $ mkData (mixHash 2243 $ hash u) (u.depth + 1) u.hasMVar u.hasParam

def mkLevelMax (u v : Level) :=
  Level.max u v $ mkData (mixHash 2251 $ mixHash (hash u) (hash v)) (Nat.max u.depth v.depth + 1)
     (u.hasMVar || v.hasMVar)
     (u.hasParam || v.hasParam)

def mkLevelIMax (u v : Level) :=
  Level.imax u v $ mkData (mixHash 2267 $ mixHash (hash u) (hash v)) (Nat.max u.depth v.depth + 1)
     (u.hasMVar || v.hasMVar)
     (u.hasParam || v.hasParam)

def levelOne := mkLevelSucc levelZero

@[export lean_level_mk_zero] def mkLevelZeroEx : Unit → Level := fun _ => levelZero
@[export lean_level_mk_succ] def mkLevelSuccEx : Level → Level := mkLevelSucc
@[export lean_level_mk_mvar] def mkLevelMVarEx : MVarId → Level := mkLevelMVar
@[export lean_level_mk_param] def mkLevelParamEx : Name → Level := mkLevelParam
@[export lean_level_mk_max] def mkLevelMaxEx : Level → Level → Level := mkLevelMax
@[export lean_level_mk_imax] def mkLevelIMaxEx : Level → Level → Level := mkLevelIMax

namespace Level

def isZero : Level → Bool
  | zero _ => true
  | _      => false

def isSucc : Level → Bool
  | succ .. => true
  | _       => false

def isMax : Level → Bool
  | max .. => true
  | _      => false

def isIMax : Level → Bool
  | imax .. => true
  | _       => false

def isMaxIMax : Level → Bool
  | max ..  => true
  | imax .. => true
  | _       => false

def isParam : Level → Bool
  | param .. => true
  | _        => false

def isMVar : Level → Bool
  | mvar .. => true
  | _       => false

def mvarId! : Level → MVarId
  | mvar mvarId _ => mvarId
  | _             => panic! "metavariable expected"

/-- If result is true, then forall assignments `A` which assigns all parameters and metavariables occuring
    in `l`, `l[A] != zero` -/
def isNeverZero : Level → Bool
  | zero _       => false
  | param ..     => false
  | mvar ..      => false
  | succ ..      => true
  | max l₁ l₂ _  => isNeverZero l₁ || isNeverZero l₂
  | imax l₁ l₂ _ => isNeverZero l₂

def ofNat : Nat → Level
  | 0   => levelZero
  | n+1 => mkLevelSucc (ofNat n)

def addOffsetAux : Nat → Level → Level
  | 0,     u => u
  | (n+1), u => addOffsetAux n (mkLevelSucc u)

def addOffset (u : Level) (n : Nat) : Level :=
  u.addOffsetAux n

def isExplicit : Level → Bool
  | zero _   => true
  | succ u _ => !u.hasMVar && !u.hasParam && isExplicit u
  | _        => false

def getOffsetAux : Level → Nat → Nat
  | succ u _, r => getOffsetAux u (r+1)
  | _,        r => r

def getOffset (lvl : Level) : Nat :=
  getOffsetAux lvl 0

def getLevelOffset : Level → Level
  | succ u _ => getLevelOffset u
  | u        => u

def toNat (lvl : Level) : Option Nat :=
  match lvl.getLevelOffset with
  | zero _ => lvl.getOffset
  | _      => none

@[extern "lean_level_eq"]
protected constant beq (a : @& Level) (b : @& Level) : Bool

instance : BEq Level := ⟨Level.beq⟩

/-- `occurs u l` return `true` iff `u` occurs in `l`. -/
def occurs : Level → Level → Bool
  | u, v@(succ v₁ _)     => u == v || occurs u v₁
  | u, v@(max v₁ v₂ _)   => u == v || occurs u v₁ || occurs u v₂
  | u, v@(imax v₁ v₂ _)  => u == v || occurs u v₁ || occurs u v₂
  | u, v                 => u == v

def ctorToNat : Level → Nat
  | zero ..  => 0
  | param .. => 1
  | mvar ..  => 2
  | succ ..  => 3
  | max ..   => 4
  | imax ..  => 5

/- TODO: use well founded recursion. -/
partial def normLtAux : Level → Nat → Level → Nat → Bool
  | succ l₁ _, k₁, l₂, k₂ => normLtAux l₁ (k₁+1) l₂ k₂
  | l₁, k₁, succ l₂ _, k₂ => normLtAux l₁ k₁ l₂ (k₂+1)
  | l₁@(max l₁₁ l₁₂ _), k₁, l₂@(max l₂₁ l₂₂ _), k₂ =>
    if l₁ == l₂ then k₁ < k₂
    else if l₁₁ != l₂₁ then normLtAux l₁₁ 0 l₂₁ 0
    else normLtAux l₁₂ 0 l₂₂ 0
  | l₁@(imax l₁₁ l₁₂ _), k₁, l₂@(imax l₂₁ l₂₂ _), k₂ =>
    if l₁ == l₂ then k₁ < k₂
    else if l₁₁ != l₂₁ then normLtAux l₁₁ 0 l₂₁ 0
    else normLtAux l₁₂ 0 l₂₂ 0
  | param n₁ _, k₁, param n₂ _, k₂ => if n₁ == n₂ then k₁ < k₂ else Name.lt n₁ n₂     -- use Name.lt because it is lexicographical
  | mvar n₁ _, k₁, mvar n₂ _, k₂ => if n₁ == n₂ then k₁ < k₂ else Name.quickLt n₁.name n₂.name  -- metavariables are temporary, the actual order doesn't matter
  | l₁, k₁, l₂, k₂ => if l₁ == l₂ then k₁ < k₂ else ctorToNat l₁ < ctorToNat l₂

/--
  A total order on level expressions that has the following properties
  - `succ l` is an immediate successor of `l`.
  - `zero` is the minimal element.
 This total order is used in the normalization procedure. -/
def normLt (l₁ l₂ : Level) : Bool :=
  normLtAux l₁ 0 l₂ 0

private def isAlreadyNormalizedCheap : Level → Bool
  | zero _    => true
  | param _ _ => true
  | mvar _ _  => true
  | succ u _  => isAlreadyNormalizedCheap u
  | _         => false

/- Auxiliary function used at `normalize` -/
private def mkIMaxAux : Level → Level → Level
  | _,      u@(zero _) => u
  | zero _, u          => u
  | u₁,     u₂         => if u₁ == u₂ then u₁ else mkLevelIMax u₁ u₂

/- Auxiliary function used at `normalize` -/
@[specialize] private partial def getMaxArgsAux (normalize : Level → Level) : Level → Bool → Array Level → Array Level
  | max l₁ l₂ _, alreadyNormalized, lvls => getMaxArgsAux normalize l₂ alreadyNormalized (getMaxArgsAux normalize l₁ alreadyNormalized lvls)
  | l,           false,             lvls => getMaxArgsAux normalize (normalize l) true lvls
  | l,           true,              lvls => lvls.push l

private def accMax (result : Level) (prev : Level) (offset : Nat) : Level :=
  if result.isZero then prev.addOffset offset
  else mkLevelMax result (prev.addOffset offset)

/- Auxiliary function used at `normalize`.
   Remarks:
   - `lvls` are sorted using `normLt`
   - `extraK` is the outter offset of the `max` term. We will push it inside.
   - `i` is the current array index
   - `prev + prevK` is the "previous" level that has not been added to `result` yet.
   - `result` is the accumulator
 -/
private partial def mkMaxAux (lvls : Array Level) (extraK : Nat) (i : Nat) (prev : Level) (prevK : Nat) (result : Level) : Level :=
  if h : i < lvls.size then
    let lvl   := lvls.get ⟨i, h⟩
    let curr  := lvl.getLevelOffset
    let currK := lvl.getOffset
    if curr == prev then
      mkMaxAux lvls extraK (i+1) curr currK result
    else
      mkMaxAux lvls extraK (i+1) curr currK (accMax result prev (extraK + prevK))
  else
    accMax result prev (extraK + prevK)

/-
  Auxiliary function for `normalize`. It assumes `lvls` has been sorted using `normLt`.
  It finds the first position that is not an explicit universe. -/
private partial def skipExplicit (lvls : Array Level) (i : Nat) : Nat :=
  if h : i < lvls.size then
    let lvl := lvls.get ⟨i, h⟩
    if lvl.getLevelOffset.isZero then skipExplicit lvls (i+1) else i
  else
    i

/-
  Auxiliary function for `normalize`.
  `maxExplicit` is the maximum explicit universe level at `lvls`.
  Return true if it finds a level with offset ≥ maxExplicit.
  `i` starts at the first non explict level.
  It assumes `lvls` has been sorted using `normLt`. -/
private partial def isExplicitSubsumedAux (lvls : Array Level) (maxExplicit : Nat) (i : Nat) : Bool :=
  if h : i < lvls.size then
    let lvl := lvls.get ⟨i, h⟩
    if lvl.getOffset ≥ maxExplicit then true
    else isExplicitSubsumedAux lvls maxExplicit (i+1)
  else
    false

/- Auxiliary function for `normalize`. See `isExplicitSubsumedAux` -/
private def isExplicitSubsumed (lvls : Array Level) (firstNonExplicit : Nat) : Bool :=
  if firstNonExplicit == 0 then false
  else
    let max := (lvls.get! (firstNonExplicit - 1)).getOffset;
    isExplicitSubsumedAux lvls max firstNonExplicit

partial def normalize (l : Level) : Level :=
  if isAlreadyNormalizedCheap l then l
  else
    let k := l.getOffset
    let u := l.getLevelOffset
    match u with
    | max l₁ l₂ _ =>
      let lvls  := getMaxArgsAux normalize l₁ false #[]
      let lvls  := getMaxArgsAux normalize l₂ false lvls
      let lvls  := lvls.qsort normLt
      let firstNonExplicit := skipExplicit lvls 0
      let i := if isExplicitSubsumed lvls firstNonExplicit then firstNonExplicit else firstNonExplicit - 1
      let lvl₁  := lvls[i]
      let prev  := lvl₁.getLevelOffset
      let prevK := lvl₁.getOffset
      mkMaxAux lvls k (i+1) prev prevK levelZero
    | imax l₁ l₂ _ =>
      if l₂.isNeverZero then addOffset (normalize (mkLevelMax l₁ l₂)) k
      else
        let l₁ := normalize l₁
        let l₂ := normalize l₂
        addOffset (mkIMaxAux l₁ l₂) k
    | _ => unreachable!

/- Return true if `u` and `v` denote the same level.
   Check is currently incomplete. -/
def isEquiv (u v : Level) : Bool :=
  u == v || u.normalize == v.normalize

/-- Reduce (if possible) universe level by 1 -/
def dec : Level → Option Level
  | zero _       => none
  | param _ _    => none
  | mvar _ _     => none
  | succ l _     => l
  | max l₁ l₂ _  => OptionM.run do return mkLevelMax (← dec l₁) (← dec l₂)
  /- Remark: `mkLevelMax` in the following line is not a typo.
     If `dec l₂` succeeds, then `imax l₁ l₂` is equivalent to `max l₁ l₂`. -/
  | imax l₁ l₂ _ => OptionM.run do return mkLevelMax (←  dec l₁) (← dec l₂)


/- Level to Format/Syntax -/
namespace PP
inductive Result where
  | leaf      : Name → Result
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

def toResult : Level → Result
  | zero _       => Result.num 0
  | succ l _     => Result.succ (toResult l)
  | max l₁ l₂ _  => Result.max (toResult l₁) (toResult l₂)
  | imax l₁ l₂ _ => Result.imax (toResult l₁) (toResult l₂)
  | param n _    => Result.leaf n
  | mvar n _     =>
    let n := n.name.replacePrefix `_uniq (Name.mkSimple "?u");
    Result.leaf n

private def parenIfFalse : Format → Bool → Format
  | f, true  => f
  | f, false => f.paren

mutual
  private partial def Result.formatLst : List Result → Format
    | []    => Format.nil
    | r::rs => Format.line ++ format r false ++ formatLst rs

  partial def Result.format : Result → Bool → Format
    | Result.leaf n,         _ => Std.format n
    | Result.num k,          _ => toString k
    | Result.offset f 0,     r => format f r
    | Result.offset f (k+1), r =>
      let f' := format f false;
      parenIfFalse (f' ++ "+" ++ Std.format (k+1)) r
    | Result.maxNode fs,    r => parenIfFalse (Format.group $ "max"  ++ formatLst fs) r
    | Result.imaxNode fs,   r => parenIfFalse (Format.group $ "imax" ++ formatLst fs) r
end

protected partial def Result.quote (r : Result) (prec : Nat) : Syntax :=
  let addParen (s : Syntax) :=
    if prec > 0 then Unhygienic.run `(level| ( $s )) else s
  match r with
  | Result.leaf n         => Unhygienic.run `(level| $(mkIdent n):ident)
  | Result.num  k         => Unhygienic.run `(level| $(quote k):numLit)
  | Result.offset r 0     => Result.quote r prec
  | Result.offset r (k+1) => addParen <| Unhygienic.run `(level| $(Result.quote r 65) + $(quote (k+1)):numLit)
  | Result.maxNode rs     => addParen <| Unhygienic.run `(level| max $(rs.toArray.map (Result.quote · max_prec))*)
  | Result.imaxNode rs    => addParen <| Unhygienic.run `(level| imax $(rs.toArray.map (Result.quote · max_prec))*)

end PP

protected def format (u : Level) : Format :=
  (PP.toResult u).format true

instance : ToFormat Level where
  format u := Level.format u

instance : ToString Level where
  toString u := Format.pretty (Level.format u)

protected def quote (u : Level) (prec : Nat := 0) : Syntax :=
  (PP.toResult u).quote prec

instance : Quote Level where
  quote u := Level.quote u

end Level

/- Similar to `mkLevelMax`, but applies cheap simplifications -/
@[export lean_level_mk_max_simp]
def mkLevelMax' (u v : Level) : Level :=
  let subsumes (u v : Level) : Bool :=
    if v.isExplicit && u.getOffset ≥ v.getOffset then true
    else match u with
      | Level.max u₁ u₂ _ => v == u₁ || v == u₂
      | _ => false
  if u == v then u
  else if u.isZero then v
  else if v.isZero then u
  else if subsumes u v then u
  else if subsumes v u then v
  else if u.getLevelOffset == v.getLevelOffset then
    if u.getOffset ≥ v.getOffset then u else v
  else
    mkLevelMax u v

/- Similar to `mkLevelIMax`, but applies cheap simplifications -/
@[export lean_level_mk_imax_simp]
def mkLevelIMax' (u v : Level) : Level :=
  if v.isNeverZero then mkLevelMax' u v
  else if v.isZero then v
  else if u.isZero then v
  else if u == v then u
  else mkLevelIMax u v

namespace Level

/- The update functions here are defined using C code. They will try to avoid
   allocating new values using pointer equality.
   The hypotheses `(h : e.is...)` are used to ensure Lean will not crash
   at runtime.
   The `update*!` functions are inlined and provide a convenient way of using the
   update proofs without providing proofs.
   Note that if they are used under a match-expression, the compiler will eliminate
   the double-match. -/

@[extern "lean_level_update_succ"]
def updateSucc (lvl : Level) (newLvl : Level) (h : lvl.isSucc) : Level :=
  mkLevelSucc newLvl

@[inline] def updateSucc! (lvl : Level) (newLvl : Level) : Level :=
match lvl with
  | succ lvl d => updateSucc (succ lvl d) newLvl rfl
  | _          => panic! "succ level expected"

@[extern "lean_level_update_max"]
def updateMax (lvl : Level) (newLhs : Level) (newRhs : Level) (h : lvl.isMax) : Level :=
  mkLevelMax' newLhs newRhs

@[inline] def updateMax! (lvl : Level) (newLhs : Level) (newRhs : Level) : Level :=
  match lvl with
  | max lhs rhs d => updateMax (max lhs rhs d) newLhs newRhs rfl
  | _             => panic! "max level expected"

@[extern "lean_level_update_imax"]
def updateIMax (lvl : Level) (newLhs : Level) (newRhs : Level) (h : lvl.isIMax) : Level :=
  mkLevelIMax' newLhs newRhs

@[inline] def updateIMax! (lvl : Level) (newLhs : Level) (newRhs : Level) : Level :=
  match lvl with
  | imax lhs rhs d => updateIMax (imax lhs rhs d) newLhs newRhs rfl
  | _              => panic! "imax level expected"

def mkNaryMax : List Level → Level
  | []    => levelZero
  | [u]   => u
  | u::us => mkLevelMax' u (mkNaryMax us)

/- Level to Format -/

@[specialize] def instantiateParams (s : Name → Option Level) : Level → Level
  | u@(zero _)       => u
  | u@(succ v _)     => if u.hasParam then u.updateSucc! (instantiateParams s v) else u
  | u@(max v₁ v₂ _)  => if u.hasParam then u.updateMax! (instantiateParams s v₁) (instantiateParams s v₂) else u
  | u@(imax v₁ v₂ _) => if u.hasParam then u.updateIMax! (instantiateParams s v₁) (instantiateParams s v₂) else u
  | u@(param n _)    => match s n with
    | some u' => u'
    | none    => u
  | u           => u

end Level

open Std (HashMap HashSet PHashMap PHashSet)

abbrev LevelMap (α : Type)  := HashMap Level α
abbrev PersistentLevelMap (α : Type) := PHashMap Level α
abbrev LevelSet := HashSet Level
abbrev PersistentLevelSet := PHashSet Level
abbrev PLevelSet := PersistentLevelSet

def Level.collectMVars (u : Level) (s : MVarIdSet := {}) : MVarIdSet :=
  match u with
  | succ v _   => collectMVars v s
  | max u v _  => collectMVars u (collectMVars v s)
  | imax u v _ => collectMVars u (collectMVars v s)
  | mvar n _   => s.insert n
  | _          => s

def Level.find? (u : Level) (p : Level → Bool) : Option Level :=
  let rec visit (u : Level) : OptionM Level :=
    if p u then
      return u
    else match u with
      | succ v _   => visit v
      | max u v _  => visit u <|> visit v
      | imax u v _ => visit u <|> visit v
      | _          => failure
  visit u

def Level.any (u : Level) (p : Level → Bool) : Bool :=
  u.find? p |>.isSome

end Lean

abbrev Nat.toLevel (n : Nat) : Lean.Level :=
  Lean.Level.ofNat n
