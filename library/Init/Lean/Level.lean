/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic
import Init.Lean.Name
import Init.Lean.Format
import Init.Data.HashMap
import Init.Data.PersistentHashMap

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

def isParam : Level → Bool
| param _ => true
| _       => false

def isMVar : Level → Bool
| mvar _ => true
| _      => false

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

def toNat : Level → Option Nat
| zero       => some 0
| succ l     => Nat.succ <$> toNat l
| max l₁ l₂  => Nat.max  <$> toNat l₁ <*> toNat l₂
| imax l₁ l₂ => Nat.imax <$> toNat l₁ <*> toNat l₂
| _          => none

def toOffset : Level → Level × Nat
| zero   => (zero, 0)
| succ l => let (l', k) := toOffset l; (l', k+1)
| l      => (l, 0)

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
protected constant hash (n : @& Level) : USize := default USize

instance hashable : Hashable Level := ⟨Level.hash⟩

@[extern "lean_level_eq"]
protected constant beq (a : @& Level) (b : @& Level) : Bool := default _

instance : HasBeq Level := ⟨Level.beq⟩

/- Return true if `a` and `b` denote the same level.
   Check is currently incomplete.
   TODO: implement in Lean. -/
@[extern "lean_level_eqv"]
constant isEquiv (a : @& Level) (b : @& Level) : Bool := default _

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
