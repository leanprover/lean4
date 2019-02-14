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

attribute [extern "level_mk_succ"]  level.succ
attribute [extern "level_mk_max"]   level.max
attribute [extern "level_mk_imax"]  level.imax
attribute [extern "level_mk_param"] level.param
attribute [extern "level_mk_mvar"]  level.mvar

instance level_is_inhabited : inhabited level :=
⟨level.zero⟩

def level.has_param : level → bool
| (level.param _)    := tt
| (level.succ l)     := level.has_param l
| (level.max l₁ l₂)  := level.has_param l₁ || level.has_param l₂
| (level.imax l₁ l₂) := level.has_param l₁ || level.has_param l₂
| _                  := ff

def level.has_mvar : level → bool
| (level.mvar _)     := tt
| (level.succ l)     := level.has_param l
| (level.max l₁ l₂)  := level.has_param l₁ || level.has_param l₂
| (level.imax l₁ l₂) := level.has_param l₁ || level.has_param l₂
| _                  := ff

def level.of_nat : nat → level
| 0     := level.zero
| (n+1) := level.succ (level.of_nat n)

def nat.imax (n m : nat) : nat :=
if m = 0 then 0 else nat.max n m

def level.to_nat : level → option nat
| level.zero         := some 0
| (level.succ l)     := nat.succ <$> level.to_nat l
| (level.max l₁ l₂)  := nat.max  <$> level.to_nat l₁ <*> level.to_nat l₂
| (level.imax l₁ l₂) := nat.imax <$> level.to_nat l₁ <*> level.to_nat l₂
| _                  := none

def level.to_offset : level → level × nat
| level.zero     := (level.zero, 0)
| (level.succ l) := let (l', k) := level.to_offset l in (l', k+1)
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

-- Mark as opaque
@[extern "lean_level_hash"]
protected def level.hash (n : @& level) : usize :=
0 -- dummy implementation

/- level to format -/
namespace level_to_format
inductive result
| leaf      : format → result
| num       : nat → result
| offset    : result → nat → result
| max_node  : list result → result
| imax_node : list result → result

def result.succ : result → result
| (result.offset f k) := result.offset f (k+1)
| (result.num k)      := result.num (k+1)
| f                   := result.offset f 1

def result.max : result → result → result
| f (result.max_node fs) := result.max_node (f::fs)
| f₁ f₂                  := result.max_node [f₁, f₂]

def result.imax : result → result → result
| f (result.imax_node fs) := result.imax_node (f::fs)
| f₁ f₂                   := result.imax_node [f₁, f₂]

def paren_if_false : format → bool → format
| f tt := f
| f ff := f.paren

mutual def result.to_format, result_list.to_format
with result.to_format : result → bool → format
| (result.leaf f)         _ := f
| (result.num k)          _ := to_string k
| (result.offset f 0)     r := result.to_format f r
| (result.offset f (k+1)) r :=
  let f' := result.to_format f ff in
  paren_if_false (f' ++ "+" ++ to_fmt (k+1)) r
| (result.max_node fs)    r := paren_if_false (format.group $ "max" ++ result_list.to_format fs) r
| (result.imax_node fs)   r := paren_if_false (format.group $ "imax" ++ result_list.to_format fs) r
with result_list.to_format : list result → format
| []      := format.nil
| (r::rs) := format.line ++ result.to_format r ff ++ result_list.to_format rs

def level.to_result : level → result
| level.zero         := result.num 0
| (level.succ l)     := result.succ (level.to_result l)
| (level.max l₁ l₂)  := result.max (level.to_result l₁) (level.to_result l₂)
| (level.imax l₁ l₂) := result.imax (level.to_result l₁) (level.to_result l₂)
| (level.param n)    := result.leaf (to_fmt n)
| (level.mvar n)     := result.leaf (to_fmt n)

def level.to_format (l : level) : format :=
(level.to_result l).to_format tt

instance level_has_to_format : has_to_format level := ⟨level.to_format⟩
instance level_has_to_string : has_to_string level := ⟨format.pretty ∘ level.to_format⟩
end level_to_format

end lean
