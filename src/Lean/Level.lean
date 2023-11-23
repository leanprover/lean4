/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.HashMap
import Lean.Data.HashSet
import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet
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

def Level.mkData (h : UInt64) (depth : Nat := 0) (hasMVar hasParam : Bool := false) : Level.Data :=
  if depth > Nat.pow 2 24 - 1 then panic! "universe level depth is too big"
  else
    let r : UInt64 := h.toUInt32.toUInt64 + hasMVar.toUInt64.shiftLeft 32 + hasParam.toUInt64.shiftLeft 33 + depth.toUInt64.shiftLeft 40
    r

instance : Repr Level.Data where
  reprPrec v prec := Id.run do
    let mut r := "Level.mkData " ++ toString v.hash
    if v.depth != 0 then
      r := r ++ " (depth := " ++ toString v.depth ++ ")"
    if v.hasMVar then
      r := r ++ " (hasMVar := " ++ toString v.hasMVar ++ ")"
    if v.hasParam then
      r := r ++ " (hasParam := " ++ toString v.hasParam ++ ")"
    Repr.addAppParen r prec

open Level

/-- Universe level metavariable Id   -/
structure LevelMVarId where
  name : Name
  deriving Inhabited, BEq, Hashable, Repr

/-- Short for `LevelMVarId` -/
abbrev LMVarId := LevelMVarId

instance : Repr LMVarId where
  reprPrec n p := reprPrec n.name p

def LMVarIdSet := RBTree LMVarId (Name.quickCmp ·.name ·.name)
  deriving Inhabited, EmptyCollection

instance : ForIn m LMVarIdSet LMVarId := inferInstanceAs (ForIn _ (RBTree ..) ..)

def LMVarIdMap (α : Type) := RBMap LMVarId α (Name.quickCmp ·.name ·.name)

instance : EmptyCollection (LMVarIdMap α) := inferInstanceAs (EmptyCollection (RBMap ..))

instance : ForIn m (LMVarIdMap α) (LMVarId × α) := inferInstanceAs (ForIn _ (RBMap ..) ..)

instance : Inhabited (LMVarIdMap α) where
  default := {}

inductive Level where
  | zero   : Level
  | succ   : Level → Level
  | max    : Level → Level → Level
  | imax   : Level → Level → Level
  | param  : Name → Level
  | mvar   : LMVarId → Level
with
  @[computed_field] data : Level → Data
    | .zero => mkData 2221 0 false false
    | .mvar mvarId => mkData (mixHash 2237 <| hash mvarId) 0 true false
    | .param name => mkData (mixHash 2239 <| hash name) 0 false true
    | .succ u => mkData (mixHash 2243 <| u.data.hash) (u.data.depth.toNat + 1) u.data.hasMVar u.data.hasParam
    | .max u v => mkData (mixHash 2251 <| mixHash (u.data.hash) (v.data.hash)) (Nat.max u.data.depth.toNat v.data.depth.toNat + 1)
       (u.data.hasMVar || v.data.hasMVar) (u.data.hasParam || v.data.hasParam)
    | .imax u v => mkData (mixHash 2267 <| mixHash (u.data.hash) (v.data.hash)) (Nat.max u.data.depth.toNat v.data.depth.toNat + 1)
       (u.data.hasMVar || v.data.hasMVar) (u.data.hasParam || v.data.hasParam)

deriving Inhabited, Repr

namespace Level

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
  Level.zero

def mkLevelMVar (mvarId : LMVarId) :=
  Level.mvar mvarId

def mkLevelParam (name : Name) :=
  Level.param name

def mkLevelSucc (u : Level) :=
  Level.succ u

def mkLevelMax (u v : Level) :=
  Level.max u v

def mkLevelIMax (u v : Level) :=
  Level.imax u v

def levelOne := mkLevelSucc levelZero

@[export lean_level_mk_zero] def mkLevelZeroEx : Unit → Level := fun _ => levelZero
@[export lean_level_mk_succ] def mkLevelSuccEx : Level → Level := mkLevelSucc
@[export lean_level_mk_mvar] def mkLevelMVarEx : LMVarId → Level := mkLevelMVar
@[export lean_level_mk_param] def mkLevelParamEx : Name → Level := mkLevelParam
@[export lean_level_mk_max] def mkLevelMaxEx : Level → Level → Level := mkLevelMax
@[export lean_level_mk_imax] def mkLevelIMaxEx : Level → Level → Level := mkLevelIMax

namespace Level

def isZero : Level → Bool
  | zero   => true
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

def mvarId! : Level → LMVarId
  | mvar mvarId => mvarId
  | _           => panic! "metavariable expected"

/-- If result is true, then forall assignments `A` which assigns all parameters and metavariables occurring
    in `l`, `l[A] != zero` -/
def isNeverZero : Level → Bool
  | zero         => false
  | param ..     => false
  | mvar ..      => false
  | succ ..      => true
  | max l₁ l₂    => isNeverZero l₁ || isNeverZero l₂
  | imax _  l₂   => isNeverZero l₂

def ofNat : Nat → Level
  | 0   => levelZero
  | n+1 => mkLevelSucc (ofNat n)

instance instOfNat (n : Nat) : OfNat Level n where
  ofNat := ofNat n

def addOffsetAux : Nat → Level → Level
  | 0,     u => u
  | (n+1), u => addOffsetAux n (mkLevelSucc u)

def addOffset (u : Level) (n : Nat) : Level :=
  u.addOffsetAux n

def isExplicit : Level → Bool
  | zero     => true
  | succ u   => !u.hasMVar && !u.hasParam && isExplicit u
  | _        => false

def getOffsetAux : Level → Nat → Nat
  | succ u  , r => getOffsetAux u (r+1)
  | _,        r => r

def getOffset (lvl : Level) : Nat :=
  getOffsetAux lvl 0

def getLevelOffset : Level → Level
  | succ u   => getLevelOffset u
  | u        => u

def toNat (lvl : Level) : Option Nat :=
  match lvl.getLevelOffset with
  | zero   => lvl.getOffset
  | _      => none

@[extern "lean_level_eq"]
protected opaque beq (a : @& Level) (b : @& Level) : Bool

instance : BEq Level := ⟨Level.beq⟩

/-- `occurs u l` return `true` iff `u` occurs in `l`. -/
def occurs : Level → Level → Bool
  | u, v@(succ v₁  )     => u == v || occurs u v₁
  | u, v@(max v₁ v₂  )   => u == v || occurs u v₁ || occurs u v₂
  | u, v@(imax v₁ v₂  )  => u == v || occurs u v₁ || occurs u v₂
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
  | succ l₁, k₁, l₂, k₂ => normLtAux l₁ (k₁+1) l₂ k₂
  | l₁, k₁, succ l₂, k₂ => normLtAux l₁ k₁ l₂ (k₂+1)
  | l₁@(max l₁₁ l₁₂), k₁, l₂@(max l₂₁ l₂₂), k₂ =>
    if l₁ == l₂ then k₁ < k₂
    else if l₁₁ != l₂₁ then normLtAux l₁₁ 0 l₂₁ 0
    else normLtAux l₁₂ 0 l₂₂ 0
  | l₁@(imax l₁₁ l₁₂), k₁, l₂@(imax l₂₁ l₂₂), k₂ =>
    if l₁ == l₂ then k₁ < k₂
    else if l₁₁ != l₂₁ then normLtAux l₁₁ 0 l₂₁ 0
    else normLtAux l₁₂ 0 l₂₂ 0
  | param n₁, k₁, param n₂, k₂ => if n₁ == n₂ then k₁ < k₂ else Name.lt n₁ n₂ -- use `Name.lt` because it is lexicographical
  /-
    We also use `Name.lt` in the following case to make sure universe parameters in a declaration
    are not affected by shifted indices. We used to use `Name.quickLt` which is not stable over shifted indices (the hashcodes change),
    and changes to the elaborator could affect the universe parameters and break code that relies on an explicit order.
    Example: test `tests/lean/343.lean`.
   -/
  | mvar n₁, k₁, mvar n₂, k₂ => if n₁ == n₂ then k₁ < k₂ else Name.lt n₁.name n₂.name
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
  | succ u  => isAlreadyNormalizedCheap u
  | _       => false

/- Auxiliary function used at `normalize` -/
private def mkIMaxAux : Level → Level → Level
  | _,    zero => zero
  | zero, u    => u
  | u₁,   u₂   => if u₁ == u₂ then u₁ else mkLevelIMax u₁ u₂

/- Auxiliary function used at `normalize` -/
@[specialize] private partial def getMaxArgsAux (normalize : Level → Level) : Level → Bool → Array Level → Array Level
  | max l₁ l₂, alreadyNormalized, lvls => getMaxArgsAux normalize l₂ alreadyNormalized (getMaxArgsAux normalize l₁ alreadyNormalized lvls)
  | l,           false,             lvls => getMaxArgsAux normalize (normalize l) true lvls
  | l,           true,              lvls => lvls.push l

private def accMax (result : Level) (prev : Level) (offset : Nat) : Level :=
  if result.isZero then prev.addOffset offset
  else mkLevelMax result (prev.addOffset offset)

/- Auxiliary function used at `normalize`.
   Remarks:
   - `lvls` are sorted using `normLt`
   - `extraK` is the outer offset of the `max` term. We will push it inside.
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

/--
Auxiliary function for `normalize`.
`maxExplicit` is the maximum explicit universe level at `lvls`.
Return true if it finds a level with offset ≥ maxExplicit.
`i` starts at the first non explicit level.
It assumes `lvls` has been sorted using `normLt`.
-/
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
    | max l₁ l₂ =>
      let lvls  := getMaxArgsAux normalize l₁ false #[]
      let lvls  := getMaxArgsAux normalize l₂ false lvls
      let lvls  := lvls.qsort normLt
      let firstNonExplicit := skipExplicit lvls 0
      let i := if isExplicitSubsumed lvls firstNonExplicit then firstNonExplicit else firstNonExplicit - 1
      let lvl₁  := lvls[i]!
      let prev  := lvl₁.getLevelOffset
      let prevK := lvl₁.getOffset
      mkMaxAux lvls k (i+1) prev prevK levelZero
    | imax l₁ l₂ =>
      if l₂.isNeverZero then addOffset (normalize (mkLevelMax l₁ l₂)) k
      else
        let l₁ := normalize l₁
        let l₂ := normalize l₂
        addOffset (mkIMaxAux l₁ l₂) k
    | _ => unreachable!

/--
Return true if `u` and `v` denote the same level.
Check is currently incomplete.
-/
def isEquiv (u v : Level) : Bool :=
  u == v || u.normalize == v.normalize

/-- Reduce (if possible) universe level by 1 -/
def dec : Level → Option Level
  | zero       => none
  | param _    => none
  | mvar _     => none
  | succ l     => l
  | max l₁ l₂  => return mkLevelMax (← dec l₁) (← dec l₂)
  /- Remark: `mkLevelMax` in the following line is not a typo.
     If `dec l₂` succeeds, then `imax l₁ l₂` is equivalent to `max l₁ l₂`. -/
  | imax l₁ l₂ => return mkLevelMax (←  dec l₁) (← dec l₂)


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
  | zero       => Result.num 0
  | succ l     => Result.succ (toResult l)
  | max l₁ l₂  => Result.max (toResult l₁) (toResult l₂)
  | imax l₁ l₂ => Result.imax (toResult l₁) (toResult l₂)
  | param n    => Result.leaf n
  | mvar n     =>
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
    | Result.maxNode fs,    r => parenIfFalse (Format.group <| "max"  ++ formatLst fs) r
    | Result.imaxNode fs,   r => parenIfFalse (Format.group <| "imax" ++ formatLst fs) r
end

protected partial def Result.quote (r : Result) (prec : Nat) : Syntax.Level :=
  let addParen (s : Syntax.Level) :=
    if prec > 0 then Unhygienic.run `(level| ( $s )) else s
  match r with
  | Result.leaf n         => Unhygienic.run `(level| $(mkIdent n):ident)
  | Result.num  k         => Unhygienic.run `(level| $(quote k):num)
  | Result.offset r 0     => Result.quote r prec
  | Result.offset r (k+1) => addParen <| Unhygienic.run `(level| $(Result.quote r 65) + $(quote (k+1)):num)
  | Result.maxNode rs     => addParen <| Unhygienic.run `(level| max $(rs.toArray.map (Result.quote · max_prec))*)
  | Result.imaxNode rs    => addParen <| Unhygienic.run `(level| imax $(rs.toArray.map (Result.quote · max_prec))*)

end PP

protected def format (u : Level) : Format :=
  (PP.toResult u).format true

instance : ToFormat Level where
  format u := Level.format u

instance : ToString Level where
  toString u := Format.pretty (Level.format u)

protected def quote (u : Level) (prec : Nat := 0) : Syntax.Level :=
  (PP.toResult u).quote prec

instance : Quote Level `level where
  quote := Level.quote

end Level

@[inline] private def mkLevelMaxCore (u v : Level) (elseK : Unit → Level) : Level :=
  let subsumes (u v : Level) : Bool :=
    if v.isExplicit && u.getOffset ≥ v.getOffset then true
    else match u with
      | Level.max u₁ u₂ => v == u₁ || v == u₂
      | _ => false
  if u == v then u
  else if u.isZero then v
  else if v.isZero then u
  else if subsumes u v then u
  else if subsumes v u then v
  else if u.getLevelOffset == v.getLevelOffset then
    if u.getOffset ≥ v.getOffset then u else v
  else
    elseK ()

/- Similar to `mkLevelMax`, but applies cheap simplifications -/
def mkLevelMax' (u v : Level) : Level :=
  mkLevelMaxCore u v fun _ => mkLevelMax u v

def simpLevelMax' (u v : Level) (d : Level) : Level :=
  mkLevelMaxCore u v fun _ => d

@[inline] private def mkLevelIMaxCore (u v : Level) (elseK : Unit → Level) : Level :=
  if v.isNeverZero then mkLevelMax' u v
  else if v.isZero then v
  else if u.isZero then v
  else if u == v then u
  else elseK ()

/- Similar to `mkLevelIMax`, but applies cheap simplifications -/
def mkLevelIMax' (u v : Level) : Level :=
  mkLevelIMaxCore u v fun _ => mkLevelIMax u v

def simpLevelIMax' (u v : Level) (d : Level) :=
  mkLevelIMaxCore u v fun _ => d

namespace Level

/-!
The update functions try to avoid allocating new values using pointer equality.
Note that if the `update*!` functions are used under a match-expression,
the compiler will eliminate the double-match.
-/

@[inline] private unsafe def updateSucc!Impl (lvl : Level) (newLvl : Level) : Level :=
  match lvl with
  | succ l => if ptrEq l newLvl then lvl else mkLevelSucc newLvl
  | _      => panic! "succ level expected"

@[implemented_by updateSucc!Impl]
def updateSucc! (lvl : Level) (newLvl : Level) : Level :=
  match lvl with
  | succ _ => mkLevelSucc newLvl
  | _      => panic! "succ level expected"

@[inline] private unsafe def updateMax!Impl (lvl : Level) (newLhs : Level) (newRhs : Level) : Level :=
  match lvl with
  | max lhs rhs => if ptrEq lhs newLhs && ptrEq rhs newRhs then simpLevelMax' newLhs newRhs lvl else mkLevelMax' newLhs newRhs
  | _           => panic! "max level expected"

@[implemented_by updateMax!Impl]
def updateMax! (lvl : Level) (newLhs : Level) (newRhs : Level) : Level :=
  match lvl with
  | max _ _ => mkLevelMax' newLhs newRhs
  | _       => panic! "max level expected"

@[inline] private unsafe def updateIMax!Impl (lvl : Level) (newLhs : Level) (newRhs : Level) : Level :=
  match lvl with
  | imax lhs rhs => if ptrEq lhs newLhs && ptrEq rhs newRhs then simpLevelIMax' newLhs newRhs lvl else mkLevelIMax' newLhs newRhs
  | _            => panic! "imax level expected"

@[implemented_by updateIMax!Impl]
def updateIMax! (lvl : Level) (newLhs : Level) (newRhs : Level) : Level :=
  match lvl with
  | imax _ _ => mkLevelIMax' newLhs newRhs
  | _        => panic! "imax level expected"

def mkNaryMax : List Level → Level
  | []    => levelZero
  | [u]   => u
  | u::us => mkLevelMax' u (mkNaryMax us)

@[specialize] def substParams (u : Level) (s : Name → Option Level) : Level :=
  go u
where
  go (u : Level) : Level :=
    match u with
    | .zero       => u
    | .succ v     => if u.hasParam then u.updateSucc! (go v) else u
    | .max v₁ v₂  => if u.hasParam then u.updateMax! (go v₁) (go v₂) else u
    | .imax v₁ v₂ => if u.hasParam then u.updateIMax! (go v₁) (go v₂) else u
    | .param n    => match s n with
      | some u' => u'
      | none    => u
    | u => u

def getParamSubst : List Name → List Level → Name → Option Level
  | p::ps, u::us, p' => if p == p' then some u else getParamSubst ps us p'
  | _,     _,     _  => none

def instantiateParams (u : Level) (paramNames : List Name) (vs : List Level) : Level :=
  u.substParams (getParamSubst paramNames vs)

def geq (u v : Level) : Bool :=
  go u.normalize v.normalize
where
  go (u v : Level) : Bool :=
    u == v ||
    match u, v with
    | _,          zero       => true
    | u,          max v₁ v₂  => go u v₁ && go u v₂
    | max u₁ u₂,  v          => go u₁ v || go u₂ v
    | u,          imax v₁ v₂ => go u v₁ && go u v₂
    | imax _  u₂, v          => go u₂ v
    | succ u,     succ v     => go u v
    | _, _ =>
      let v' := v.getLevelOffset
      (u.getLevelOffset == v' || v'.isZero)
      && u.getOffset ≥ v.getOffset
termination_by _ u v => (u, v)

end Level

abbrev LevelMap (α : Type)  := HashMap Level α
abbrev PersistentLevelMap (α : Type) := PHashMap Level α
abbrev LevelSet := HashSet Level
abbrev PersistentLevelSet := PHashSet Level
abbrev PLevelSet := PersistentLevelSet

def Level.collectMVars (u : Level) (s : LMVarIdSet := {}) : LMVarIdSet :=
  match u with
  | succ v   => collectMVars v s
  | max u v  => collectMVars u (collectMVars v s)
  | imax u v => collectMVars u (collectMVars v s)
  | mvar n   => s.insert n
  | _        => s

def Level.find? (u : Level) (p : Level → Bool) : Option Level :=
  let rec visit (u : Level) : Option Level :=
    if p u then
      return u
    else match u with
      | succ v   => visit v
      | max u v  => visit u <|> visit v
      | imax u v => visit u <|> visit v
      | _          => failure
  visit u

def Level.any (u : Level) (p : Level → Bool) : Bool :=
  u.find? p |>.isSome

end Lean

abbrev Nat.toLevel (n : Nat) : Lean.Level :=
  Lean.Level.ofNat n
