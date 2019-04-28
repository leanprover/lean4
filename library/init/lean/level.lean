/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.option.basic init.lean.name init.lean.format

namespace Lean

inductive Level
| zero   : Level
| succ   : Level → Level
| max    : Level → Level → Level
| imax   : Level → Level → Level
| Param  : Name → Level
| mvar   : Name → Level

attribute [extern "level_mk_succ"]  Level.succ
attribute [extern "level_mk_max"]   Level.max
attribute [extern "level_mk_imax"]  Level.imax
attribute [extern "level_mk_param"] Level.Param
attribute [extern "level_mk_mvar"]  Level.mvar

instance levelIsInhabited : Inhabited Level :=
⟨Level.zero⟩

def Level.one : Level := Level.succ Level.zero

def Level.hasParam : Level → Bool
| (Level.Param _)    := true
| (Level.succ l)     := Level.hasParam l
| (Level.max l₁ l₂)  := Level.hasParam l₁ || Level.hasParam l₂
| (Level.imax l₁ l₂) := Level.hasParam l₁ || Level.hasParam l₂
| _                  := false

def Level.hasMvar : Level → Bool
| (Level.mvar _)     := true
| (Level.succ l)     := Level.hasParam l
| (Level.max l₁ l₂)  := Level.hasParam l₁ || Level.hasParam l₂
| (Level.imax l₁ l₂) := Level.hasParam l₁ || Level.hasParam l₂
| _                  := false

def Level.ofNat : Nat → Level
| 0     := Level.zero
| (n+1) := Level.succ (Level.ofNat n)

def Nat.imax (n m : Nat) : Nat :=
if m = 0 then 0 else Nat.max n m

def Level.toNat : Level → Option Nat
| Level.zero         := some 0
| (Level.succ l)     := Nat.succ <$> Level.toNat l
| (Level.max l₁ l₂)  := Nat.max  <$> Level.toNat l₁ <*> Level.toNat l₂
| (Level.imax l₁ l₂) := Nat.imax <$> Level.toNat l₁ <*> Level.toNat l₂
| _                  := none

def Level.toOffset : Level → Level × Nat
| Level.zero     := (Level.zero, 0)
| (Level.succ l) := let (l', k) := Level.toOffset l in (l', k+1)
| l              := (l, 0)

def Level.instantiate (s : Name → Option Level) : Level → Level
| Level.zero         := Level.zero
| (Level.succ l)     := Level.succ (Level.instantiate l)
| (Level.max l₁ l₂)  := Level.max (Level.instantiate l₁) (Level.instantiate l₂)
| (Level.imax l₁ l₂) := Level.imax (Level.instantiate l₁) (Level.instantiate l₂)
| l@(Level.Param n)  :=
  (match s n with
   | some l' := l'
   | none    := l)
| l                  := l

@[extern "lean_level_hash"]
constant Level.hash (n : @& Level) : USize := default USize

/- Level to Format -/
namespace LevelToFormat
inductive Result
| leaf      : Format → Result
| num       : Nat → Result
| offset    : Result → Nat → Result
| maxNode   : List Result → Result
| imaxNode  : List Result → Result

def Result.succ : Result → Result
| (Result.offset f k) := Result.offset f (k+1)
| (Result.num k)      := Result.num (k+1)
| f                   := Result.offset f 1

def Result.max : Result → Result → Result
| f (Result.maxNode Fs) := Result.maxNode (f::Fs)
| f₁ f₂                 := Result.maxNode [f₁, f₂]

def Result.imax : Result → Result → Result
| f (Result.imaxNode Fs) := Result.imaxNode (f::Fs)
| f₁ f₂                  := Result.imaxNode [f₁, f₂]

def parenIfFalse : Format → Bool → Format
| f true  := f
| f false := f.paren

@[specialize] private def formatLst (fmt : Result → Format) : List Result → Format
| []      := Format.nil
| (r::rs) := Format.line ++ fmt r ++ formatLst rs

partial def Result.format : Result → Bool → Format
| (Result.leaf f)         _ := f
| (Result.num k)          _ := toString k
| (Result.offset f 0)     r := Result.format f r
| (Result.offset f (k+1)) r :=
  let f' := Result.format f false in
  parenIfFalse (f' ++ "+" ++ fmt (k+1)) r
| (Result.maxNode fs)    r := parenIfFalse (Format.group $ "max"  ++ formatLst (λ r, Result.format r false) fs) r
| (Result.imaxNode fs)   r := parenIfFalse (Format.group $ "imax" ++ formatLst (λ r, Result.format r false) fs) r

def Level.toResult : Level → Result
| Level.zero         := Result.num 0
| (Level.succ l)     := Result.succ (Level.toResult l)
| (Level.max l₁ l₂)  := Result.max (Level.toResult l₁) (Level.toResult l₂)
| (Level.imax l₁ l₂) := Result.imax (Level.toResult l₁) (Level.toResult l₂)
| (Level.Param n)    := Result.leaf (fmt n)
| (Level.mvar n)     := Result.leaf (fmt n)

def Level.format (l : Level) : Format :=
(Level.toResult l).format true

instance levelHasFormat : HasFormat Level := ⟨Level.format⟩
instance levelHasToString : HasToString Level := ⟨Format.pretty ∘ Level.format⟩
end LevelToFormat

end Lean
