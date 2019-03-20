/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name init.data.option.basic

namespace lean

inductive level
| zero   : level
| succ   : level → level
| max    : level → level → level
| imax   : level → level → level
| param  : name → level
| mvar   : name → level

attribute [extern "levelMkSucc"]  level.succ
attribute [extern "levelMkMax"]   level.max
attribute [extern "levelMkImax"]  level.imax
attribute [extern "levelMkParam"] level.param
attribute [extern "levelMkMvar"]  level.mvar

instance levelIsInhabited : inhabited level :=
⟨level.zero⟩

def level.one : level := level.succ level.zero

def level.hasParam : level → bool
| (level.param _)    := tt
| (level.succ l)     := level.hasParam l
| (level.max l₁ l₂)  := level.hasParam l₁ || level.hasParam l₂
| (level.imax l₁ l₂) := level.hasParam l₁ || level.hasParam l₂
| _                  := ff

def level.hasMvar : level → bool
| (level.mvar _)     := tt
| (level.succ l)     := level.hasParam l
| (level.max l₁ l₂)  := level.hasParam l₁ || level.hasParam l₂
| (level.imax l₁ l₂) := level.hasParam l₁ || level.hasParam l₂
| _                  := ff

def level.ofNat : nat → level
| 0     := level.zero
| (n+1) := level.succ (level.ofNat n)

def nat.imax (n m : nat) : nat :=
if m = 0 then 0 else nat.max n m

def level.toNat : level → option nat
| level.zero         := some 0
| (level.succ l)     := nat.succ <$> level.toNat l
| (level.max l₁ l₂)  := nat.max  <$> level.toNat l₁ <*> level.toNat l₂
| (level.imax l₁ l₂) := nat.imax <$> level.toNat l₁ <*> level.toNat l₂
| _                  := none

def level.toOffset : level → level × nat
| level.zero     := (level.zero, 0)
| (level.succ l) := let (l', k) := level.toOffset l in (l', k+1)
| l              := (l, 0)

def level.instantiate (s : name → option level) : level → level
| level.zero         := level.zero
| (level.succ l)     := level.succ (level.instantiate l)
| (level.max l₁ l₂)  := level.max (level.instantiate l₁) (level.instantiate l₂)
| (level.imax l₁ l₂) := level.imax (level.instantiate l₁) (level.instantiate l₂)
| l@(level.param n)  :=
  (match s n with
   | some l' := l'
   | none    := l)
| l                  := l

@[extern "leanLevelHash"]
constant level.hash (n : @& level) : usize := default usize

/- level to format -/
namespace levelToFormat
inductive result
| leaf      : format → result
| num       : nat → result
| offset    : result → nat → result
| maxNode  : list result → result
| imaxNode : list result → result

def result.succ : result → result
| (result.offset f k) := result.offset f (k+1)
| (result.num k)      := result.num (k+1)
| f                   := result.offset f 1

def result.max : result → result → result
| f (result.maxNode fs) := result.maxNode (f::fs)
| f₁ f₂                  := result.maxNode [f₁, f₂]

def result.imax : result → result → result
| f (result.imaxNode fs) := result.imaxNode (f::fs)
| f₁ f₂                   := result.imaxNode [f₁, f₂]

def parenIfFalse : format → bool → format
| f tt := f
| f ff := f.paren

mutual def result.toFormat, resultList.toFormat
with result.toFormat : result → bool → format
| (result.leaf f)         _ := f
| (result.num k)          _ := toString k
| (result.offset f 0)     r := result.toFormat f r
| (result.offset f (k+1)) r :=
  let f' := result.toFormat f ff in
  parenIfFalse (f' ++ "+" ++ toFmt (k+1)) r
| (result.maxNode fs)    r := parenIfFalse (format.group $ "max" ++ resultList.toFormat fs) r
| (result.imaxNode fs)   r := parenIfFalse (format.group $ "imax" ++ resultList.toFormat fs) r
with resultList.toFormat : list result → format
| []      := format.nil
| (r::rs) := format.line ++ result.toFormat r ff ++ resultList.toFormat rs

def level.toResult : level → result
| level.zero         := result.num 0
| (level.succ l)     := result.succ (level.toResult l)
| (level.max l₁ l₂)  := result.max (level.toResult l₁) (level.toResult l₂)
| (level.imax l₁ l₂) := result.imax (level.toResult l₁) (level.toResult l₂)
| (level.param n)    := result.leaf (toFmt n)
| (level.mvar n)     := result.leaf (toFmt n)

def level.toFormat (l : level) : format :=
(level.toResult l).toFormat tt

instance levelHasToFormat : hasToFormat level := ⟨level.toFormat⟩
instance levelHasToString : hasToString level := ⟨format.pretty ∘ level.toFormat⟩
end levelToFormat

end lean
