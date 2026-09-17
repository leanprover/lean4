/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Array.QSort
public import Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
public import Lean.Hygiene
public import Lean.Data.Name
public import Lean.Data.Format
public import Init.Data.Option.Coe
public import Std.Data.TreeSet.Basic
public import Std.Internal.Order.Basic
public import Init.ByCases
public import Init.Data.Nat.Internal.Linear

public section

namespace Lean

-- This is intentionally in the `Lean` namespace to avoid polluting the `Nat` namespace.
def Nat.imax (n m : Nat) : Nat :=
  if m = 0 then 0 else Nat.max n m

/--
 Cached hash code, cached results, and other data for `Level`.
   hash      : 32-bits
   hasMVar   : 1-bit
   hasParam  : 1-bit
   depth     : 24-bits -/
@[expose] def Level.Data := UInt64

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

@[extern "lean_level_mk_data"]
opaque Level.mkData (h : UInt64) (depth : Nat := 0) (hasMVar hasParam : Bool := false) : Level.Data

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

@[expose] def LMVarIdSet := Std.TreeSet LMVarId (Name.quickCmp ·.name ·.name)
  deriving Inhabited, EmptyCollection

instance [Monad m] : ForIn m LMVarIdSet LMVarId := inferInstanceAs (ForIn _ (Std.TreeSet _ _) ..)

@[expose] def LMVarIdMap (α : Type) := Std.TreeMap LMVarId α (Name.quickCmp ·.name ·.name)

instance : EmptyCollection (LMVarIdMap α) := inferInstanceAs (EmptyCollection (Std.TreeMap _ _ _))

instance [Monad m] : ForIn m (LMVarIdMap α) (LMVarId × α) := inferInstanceAs (ForIn _ (Std.TreeMap _ _ _) ..)

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

@[deprecated Level.zero (since := "2026-02-27")] -- This was previously required in order to get the computed field `data` to work, but it is no longer needed.
abbrev levelZero := Level.zero

def mkLevelMVar (mvarId : LMVarId) :=
  Level.mvar mvarId

def mkLevelParam (name : Name) :=
  Level.param name

@[expose] def mkLevelSucc (u : Level) :=
  Level.succ u

def mkLevelMax (u v : Level) :=
  Level.max u v

def mkLevelIMax (u v : Level) :=
  Level.imax u v

abbrev Level.one := mkLevelSucc .zero

@[deprecated Level.one (since := "2026-02-27")]
abbrev levelOne := Level.one

@[export lean_level_mk_zero] def mkLevelZeroEx : Unit → Level := fun _ => .zero
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

/--
Returns true if and only if `l` evaluates to zero for all instantiations of parameters and
meta-variables.
-/
def isAlwaysZero : Level → Bool
  | zero         => true
  | param ..     => false
  | mvar ..      => false
  | succ ..      => false
  | max l₁ l₂    => isAlwaysZero l₁ && isAlwaysZero l₂
  | imax _  l₂   => isAlwaysZero l₂

@[expose, implicit_reducible] def ofNat : Nat → Level
  | 0   => Level.zero
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

def normLtAux : Level → Nat → Level → Nat → Bool
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

def isAlreadyNormalizedCheap : Level → Bool
  | zero    => true
  | param _ => true
  | mvar _  => true
  | succ u  => isAlreadyNormalizedCheap u
  | _       => false

/-- Auxiliary function used at `normalize` -/
private def mkIMaxAux : Level → Level → Level
  | _,    zero   => zero
  | zero, u      => u
  | succ zero, u => u
  | u₁,   u₂     => if u₁ == u₂ then u₁ else mkLevelIMax u₁ u₂

/-- Auxiliary function used at `normalize` -/
@[specialize] private partial def getMaxArgsAux (normalize : Level → Level) : Level → Bool → Array Level → Array Level
  | max l₁ l₂, alreadyNormalized, lvls => getMaxArgsAux normalize l₂ alreadyNormalized (getMaxArgsAux normalize l₁ alreadyNormalized lvls)
  | l,           false,             lvls => getMaxArgsAux normalize (normalize l) true lvls
  | l,           true,              lvls => lvls.push l

private def accMax (result : Level) (prev : Level) (offset : Nat) : Level :=
  if result.isZero then prev.addOffset offset
  else mkLevelMax result (prev.addOffset offset)

/--
   Auxiliary function used at `normalize`.
   Remarks:
   - `lvls` are sorted using `normLt`
   - `extraK` is the outer offset of the `max` term. We will push it inside.
   - `i` is the current array index
   - `prev + prevK` is the "previous" level that has not been added to `result` yet.
   - `result` is the accumulator
-/
private partial def mkMaxAux (lvls : Array Level) (extraK : Nat) (i : Nat) (prev : Level) (prevK : Nat) (result : Level) : Level :=
  if h : i < lvls.size then
    let lvl   := lvls[i]
    let curr  := lvl.getLevelOffset
    let currK := lvl.getOffset
    if curr == prev then
      mkMaxAux lvls extraK (i+1) curr currK result
    else
      mkMaxAux lvls extraK (i+1) curr currK (accMax result prev (extraK + prevK))
  else
    accMax result prev (extraK + prevK)

/--
  Auxiliary function for `normalize`. It assumes `lvls` has been sorted using `normLt`.
  It finds the first position that is not an explicit universe.
-/
private partial def skipExplicit (lvls : Array Level) (i : Nat) : Nat :=
  if h : i < lvls.size then
    let lvl := lvls[i]
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
    let lvl := lvls[i]
    if lvl.getOffset ≥ maxExplicit then true
    else isExplicitSubsumedAux lvls maxExplicit (i+1)
  else
    false

/-- Auxiliary function for `normalize`. See `isExplicitSubsumedAux` -/
private def isExplicitSubsumed (lvls : Array Level) (firstNonExplicit : Nat) : Bool :=
  if firstNonExplicit == 0 then false
  else
    let max := lvls[firstNonExplicit - 1]!.getOffset
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
      mkMaxAux lvls k (i+1) prev prevK Level.zero
    | imax l₁ l₂ =>
      if l₂.isNeverZero then addOffset (normalize (mkLevelMax l₁ l₂)) k
      else
        let l₁ := normalize l₁
        let l₂ := normalize l₂
        addOffset (mkIMaxAux l₁ l₂) k
    | _ => unreachable!

inductive SortedAssocList (α β : Type) (cmp : α → α → Ordering) where
  | nil
  | cons (k : α) (v : β) (t : SortedAssocList α β cmp)
deriving Repr, BEq

@[specialize]
def SortedAssocList.insertMax [Max β] {cmp : α → α → Ordering} (k : α) (v : β) :
    SortedAssocList α β cmp → SortedAssocList α β cmp
  | .nil => .cons k v .nil
  | a@(.cons k' v' t) =>
    match cmp k k' with
    | .lt => .cons k v a
    | .eq => .cons k' (Max.max v v') t
    | .gt => .cons k' v' (t.insertMax k v)

@[specialize]
def SortedAssocList.find? {cmp : α → α → Ordering} (k : α) :
    SortedAssocList α β cmp → Option β
  | .nil => none
  | .cons k' v' t =>
    match cmp k k' with
    | .lt => none
    | .eq => v'
    | .gt => t.find? k

@[specialize]
def SortedAssocList.merge [Max β] {cmp : α → α → Ordering} :
    SortedAssocList α β cmp → SortedAssocList α β cmp → SortedAssocList α β cmp
  | .nil, x => x
  | x, .nil => x
  | l@(.cons k v t), r@(.cons k' v' t') =>
    match cmp k k' with
    | .lt => .cons k v <| merge t r
    | .eq => .cons k (Max.max v v') <| merge t t'
    | .gt => .cons k' v' <| merge l t'
termination_by l r => sizeOf l + sizeOf r

@[specialize]
def SortedAssocList.erase {cmp : α → α → Ordering} (k : α) :
    SortedAssocList α β cmp → SortedAssocList α β cmp
  | .nil => .nil
  | a@(.cons k' v' t) =>
    match cmp k k' with
    | .lt => a
    | .eq => t
    | .gt => .cons k' v' (t.erase k)

inductive SortedSetNode (α : Type) (cmp : α → α → Ordering) : Type where
  | nil
  | cons (k : α) (t : SortedSetNode α cmp)
deriving Repr, BEq

inductive SortedSet (α : Type) (cmp : α → α → Ordering) where
  | nil
  | cons (k : α) (t : SortedSetNode α cmp)
  | never
deriving Repr, BEq

@[grind =]
def SortedSetNode.toList {cmp : α → α → Ordering} :
    SortedSetNode α cmp → List α
  | .nil => []
  | .cons k t => k :: t.toList

@[grind =]
def SortedSet.toList? {cmp : α → α → Ordering} :
    SortedSet α cmp → Option (List α)
  | .nil => some []
  | .cons k t => some <| k :: t.toList
  | .never => none

attribute [simp] SortedSetNode.toList
attribute [simp] SortedSet.toList?.eq_1 SortedSet.toList?.eq_2 SortedSet.toList?.eq_3

@[specialize]
def SortedSetNode.insert {cmp : α → α → Ordering} (k : α) :
    SortedSetNode α cmp → SortedSetNode α cmp
  | .nil => .cons k .nil
  | a@(.cons k' t) =>
    match cmp k k' with
    | .lt => .cons k a
    | .eq => .cons k' t
    | .gt => .cons k' (t.insert k)

@[specialize]
def SortedSet.insert {cmp : α → α → Ordering} (k : α) :
    SortedSet α cmp → SortedSet α cmp
  | .never => .never
  | .nil => .cons k .nil
  | .cons k' t =>
    match cmp k k' with
    | .lt => .cons k (.cons k' t)
    | .eq => .cons k' t
    | .gt => .cons k' (t.insert k)


@[specialize]
def SortedSetNode.contains {cmp : α → α → Ordering} (k : α) :
    SortedSetNode α cmp → Bool
  | .nil => false
  | .cons k' t =>
    match cmp k k' with
    | .lt => false
    | .eq => true
    | .gt => t.contains k

@[specialize]
def SortedSetNode.erase {cmp : α → α → Ordering} (k : α) :
    SortedSetNode α cmp → SortedSetNode α cmp
  | .nil => .nil
  | a@(.cons k' t) =>
    match cmp k k' with
    | .lt => a
    | .eq => t
    | .gt => .cons k' (t.erase k)

@[specialize]
def SortedSetNode.merge {cmp : α → α → Ordering}:
    SortedSetNode α cmp → SortedSetNode α cmp → SortedSetNode α cmp
  | .nil, x => x
  | x, .nil => x
  | l@(.cons k t), r@(.cons k' t') =>
    match cmp k k' with
    | .lt => .cons k <| merge t r
    | .eq => .cons k <| merge t t'
    | .gt => .cons k' <| merge l t'
termination_by l r => sizeOf l + sizeOf r

@[specialize]
def SortedSet.merge {cmp : α → α → Ordering} :
    SortedSet α cmp → SortedSet α cmp → SortedSet α cmp
  | .never, _ => .never
  | _, .never => .never
  | .nil, x => x
  | x, .nil => x
  | .cons k t, .cons k' t' =>
    match cmp k k' with
    | .lt => .cons k <| t.merge (.cons k' t')
    | .eq => .cons k <| t.merge t'
    | .gt => .cons k' <| SortedSetNode.merge (.cons k t) t'

mutual

structure Conditional where
  level : FlattenedLevel
  conds : SortedSetNode Name Name.quickCmp
deriving Repr

structure FlattenedLevel where
  constOff : Nat := 0
  paramOff : SortedAssocList Name Nat Name.quickCmp := .nil
  extra : List Conditional := []
deriving Repr

end

@[inline]
def FlattenedLevel.addExtra (x : FlattenedLevel) (extra : Conditional) : FlattenedLevel :=
  { x with extra := extra :: x.extra }

@[inline]
def FlattenedLevel.addParam (x : FlattenedLevel) (nm : Name) (off : Nat) : FlattenedLevel :=
  { x with paramOff := x.paramOff.insertMax nm off }

def flattenAux (l : Level) (off : Nat) (acc : FlattenedLevel)
    (zc : SortedSet Name Name.quickCmp) : FlattenedLevel × SortedSet Name Name.quickCmp :=
  match l with
  | .zero => (acc, zc)
  | .succ l' =>
    if acc.constOff ≤ off then
      flattenAux l' (off + 1) { acc with constOff := off + 1 } .never
    else
      flattenAux l' (off + 1) acc .never
  | .max l₁ l₂ =>
    let (acc, zc) := flattenAux l₁ off acc zc
    flattenAux l₂ off acc zc
  | .imax l₁ l₂ =>
    let (acc, zc') := flattenAux l₂ off acc .nil
    match zc' with
    | .never => flattenAux l₁ off acc (zc.merge zc')
    | .nil => (acc, zc)
    | .cons k t =>
      (acc.addExtra ⟨(flattenAux l₁ off { constOff := off } .never).1, .cons k t⟩, zc.merge zc')
  | .param p | .mvar ⟨p⟩ => (acc.addParam p off, zc.insert p)

def flatten (l : Level) : FlattenedLevel :=
  (flattenAux l 0 {} .never).1

def FlattenedLevel.merge (l l' : FlattenedLevel) : FlattenedLevel :=
  { l with
    constOff := l.constOff.max l'.constOff,
    paramOff := l.paramOff.merge l'.paramOff,
    extra := l.extra ++ l'.extra }

def FlattenedLevel.setZero (l : FlattenedLevel) (key : Name) : FlattenedLevel :=
  go [] l.extra
termination_by sizeOf l
decreasing_by cases l; decreasing_tactic
where
  go (newExtra : List Conditional) : List Conditional → FlattenedLevel
    | [] =>
      let l := { l with paramOff := l.paramOff.erase key }
      { l with extra := newExtra }
    | ⟨l', c⟩ :: tail =>
      let c := c.erase key
      match c with
      | .nil => go newExtra tail
      | _ =>
        let l' := setZero l' key
        go (⟨l', c⟩ :: newExtra) tail
  termination_by l => sizeOf l

def FlattenedLevel.setNonzero (l : FlattenedLevel) (key : Name) : FlattenedLevel :=
  let l :=
    match l.paramOff.find? key with
    | none => l
    | some off => { l with constOff := Max.max l.constOff (off + 1) }
  go { l with extra := [] } l.extra
termination_by sizeOf l
decreasing_by rename_i l'; cases l'; split <;> simp +arith
where
  go (l : FlattenedLevel) : List Conditional → FlattenedLevel
    | [] => l
    | ⟨l', c⟩ :: tail =>
      let l' := setNonzero l' key
      if c.contains key then
        go (l.merge l') tail
      else
        go (l.addExtra ⟨l', c⟩) tail
  termination_by l => sizeOf l

open Lean Order

instance : Lean.Order.PartialOrder Bool where
  rel a b := a → b
  rel_refl := by decide
  rel_trans := by decide
  rel_antisymm := by decide

noncomputable instance : Lean.Order.CCPO Bool where
  has_csup {p} hp := by
    by_cases h : p true
    · exists true
      simp [Lean.Order.is_sup, Lean.Order.PartialOrder.rel, h]
    · exists false
      simp [Lean.Order.is_sup, Lean.Order.PartialOrder.rel, h]

@[partial_fixpoint_monotone]
theorem monotone_and [Lean.Order.PartialOrder α] {f₁ f₂ : α → Bool}
    (h₁ : Lean.Order.monotone f₁) (h₂ : Lean.Order.monotone f₂) :
    Lean.Order.monotone fun x => f₁ x && f₂ x := by
  intro a b h
  simp only [Lean.Order.PartialOrder.rel, Bool.and_eq_true]
  intro ⟨ha, hb⟩
  exact ⟨h₁ a b h ha, h₂ a b h hb⟩

instance [inst : PartialOrder α] : PartialOrder (Id α) := inst
instance [inst : CCPO α] : CCPO (Id α) := inst

@[partial_fixpoint_monotone]
theorem Id.monotone_bind_right [PartialOrder β] [PartialOrder γ]
    (x : Id α) (f : γ → α → Id β) (h : monotone f) :
    monotone fun a => x >>= f a :=
  monotone_apply _ _ h

@[partial_fixpoint_monotone]
theorem Id.monotone_run [PartialOrder α] [PartialOrder β]
    (f : β → Id α) (h : monotone f) :
    monotone fun a => Id.run (f a) := h

@[partial_fixpoint_monotone]
theorem Id.monotone_pure [PartialOrder α] [PartialOrder β]
    (f : β → α) (h : monotone f) :
    monotone fun a => (pure (f a) : Id α) := h

def FlattenedLevel.beq (l₁ l₂ : FlattenedLevel) : Bool := Id.run do
  if l₁.constOff != l₂.constOff then
    return false
  if let a :: _ := l₁.extra then
    let .cons cond _ := a.conds | unreachable!
    return (setZero l₁ cond).beq (setZero l₂ cond) &&
      (setNonzero l₁ cond).beq (setNonzero l₂ cond)
  if let a :: _ := l₂.extra then
    let .cons cond _ := a.conds | unreachable!
    return (setZero l₁ cond).beq (setZero l₂ cond) &&
      (setNonzero l₁ cond).beq (setNonzero l₂ cond)
  return l₁.paramOff == l₂.paramOff
partial_fixpoint

/--
Return true if `u` and `v` denote the same level.
Assumes that `u` and `v` don't contain meta-variables.
-/
@[export lean_level_is_equiv]
def isEquiv (u v : Level) : Bool :=
  u == v || (flatten u).beq (flatten v)

@[inline]
private def geqCore (u v : Level) : Bool :=
  let fu := flatten u
  let fv := flatten v
  FlattenedLevel.beq fu (fu.merge fv)


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

structure Context where
  mvars : Bool
  lIndex? : LMVarId → Option Nat

abbrev M := ReaderM Context

def toResult (l : Level) : M Result := do
  match l with
  | zero       => return Result.num 0
  | succ l     => return Result.succ (← toResult l)
  | max l₁ l₂  => return Result.max (← toResult l₁) (← toResult l₂)
  | imax l₁ l₂ => return Result.imax (← toResult l₁) (← toResult l₂)
  | param n    => return Result.leaf n
  | mvar n     =>
    if !(← read).mvars then
      return Result.leaf `_
    else if let some i := (← read).lIndex? n then
      return Result.leaf <| Name.num (Name.mkSimple "?u") (i + 1)
    else
      -- Undefined mvar, use internal name
      return Result.leaf <| n.name.replacePrefix `_uniq (Name.mkSimple "?_mvar")

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
      parenIfFalse (f' ++ " + " ++ Std.format (k+1)) r
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

protected def format (u : Level) (mvars : Bool) (lIndex? : LMVarId → Option Nat) : Format :=
  (PP.toResult u) |>.run { mvars, lIndex? } |>.format true

instance : ToFormat Level where
  format u := Level.format u (mvars := true) (lIndex? := fun _ => none)

instance : ToString Level where
  toString u := Format.pretty (format u)

protected def quote (u : Level) (prec : Nat := 0) (mvars : Bool := true) (lIndex? : LMVarId → Option Nat) : Syntax.Level :=
  (PP.toResult u) |>.run { mvars, lIndex? } |>.quote prec

instance : Quote Level `level where
  quote := Level.quote (lIndex? := fun _ => none)

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

/-- Similar to `mkLevelMax`, but applies cheap simplifications -/
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

/-- Similar to `mkLevelIMax`, but applies cheap simplifications -/
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
  | []    => Level.zero
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

@[export lean_level_geq]
def geq (u v : Level) : Bool :=
  u == v || go u.normalize v.normalize || geqCore u v
where
  go (u v : Level) : Bool :=
    u == v ||
    let k := fun () =>
      match v with
      | imax v₁ v₂ => go u v₁ && go u v₂
      | _          =>
        let v' := v.getLevelOffset
        (u.getLevelOffset == v' || v'.isZero)
        && u.getOffset ≥ v.getOffset
    match u, v with
    | _,          zero      => true
    | u,          max v₁ v₂ => go u v₁ && go u v₂
    | max u₁ u₂,  v         => go u₁ v || go u₂ v || k ()
    | imax _  u₂, v         => go u₂ v
    | succ u,     succ v    => go u v
    | _,          _         => k ()
  termination_by (u, v)

end Level

abbrev LevelMap (α : Type)  := Std.HashMap Level α
abbrev PersistentLevelMap (α : Type) := PHashMap Level α
abbrev LevelSet := Std.HashSet Level
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

/--
Converts a natural number to the corresponding `Lean.Level`.

This is intentionally in the `Lean` namespace to avoid polluting the `Nat` namespace. Note that
after `open Lean`, `n.toLevel` will work for `n : Nat`.
-/
abbrev Nat.toLevel (n : Nat) : Lean.Level :=
  Lean.Level.ofNat n

end Lean
