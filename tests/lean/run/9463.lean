/-!
# `deriving Inhabited` uses structure field defaults

https://github.com/leanprover/lean4/issues/9463
-/

/-!
This used to use `false` in the `default` instance.
-/
structure Config where
  iota := true
deriving Inhabited

/-- info: true -/
#guard_msgs in #eval (default : Config).iota

/-- info: instInhabitedConfig : Inhabited Config -/
#guard_msgs in #check instInhabitedConfig

/-!
We don't require that every field have a default value.
-/
structure Config' where
  iota := true
  n : Nat
deriving Inhabited

/-- info: true -/
#guard_msgs in #eval (default : Config').iota
/-- info: 0 -/
#guard_msgs in #eval (default : Config').n

/-- info: instInhabitedConfig' : Inhabited Config' -/
#guard_msgs in #check instInhabitedConfig'

/-!
It still includes an `[Inhabited _]` parameter when needed.
-/
structure Config'' (α : Type) where
  iota := true
  n : α
deriving Inhabited

/-- info: true -/
#guard_msgs in #eval (default : Config'' Nat).iota
/-- info: 0 -/
#guard_msgs in #eval (default : Config'' Nat).n

/-- info: instInhabitedConfig'' {a✝ : Type} [Inhabited a✝] : Inhabited (Config'' a✝) -/
#guard_msgs in #check instInhabitedConfig''

/-!
In this example we can see that it adds an inhabited parameter.
Currently, even when we give a default value, the instance parameter is still added.
-/
structure Config''' (α : Type) where
  n : α → α
deriving Inhabited

/-- info: instInhabitedConfig''' {a✝ : Type} [Inhabited a✝] : Inhabited (Config''' a✝) -/
#guard_msgs in #check instInhabitedConfig'''

structure Config'''' (α : Type) where
  n : α → α := id
deriving Inhabited

/-- info: instInhabitedConfig'''' {a✝ : Type} [Inhabited a✝] : Inhabited (Config'''' a✝) -/
#guard_msgs in #check instInhabitedConfig''''

/-!
Mixed needs for `Inhabited` parameters.
Currently additional such parameters are all or nothing.
-/
structure S (α β : Type) where
  f : α → α := id
  g : β
deriving Inhabited

/--
info: instInhabitedS {a✝ : Type} [Inhabited a✝] {a✝¹ : Type} [Inhabited a✝¹] : Inhabited (S a✝ a✝¹)
-/
#guard_msgs in #check instInhabitedS

/-!
When there are structure field default value cycles, those defaults can be ignored.
-/
structure A (α : Type) where
  (x y : α)
deriving Inhabited
structure B extends A Nat where
  n : Nat := 2
  x := y + 1
  y := x + 1
deriving Inhabited

/-- info: 2 -/
#guard_msgs in #eval (default : B).n
/-- info: 0 -/
#guard_msgs in #eval (default : B).x
/-- info: 0 -/
#guard_msgs in #eval (default : B).y
