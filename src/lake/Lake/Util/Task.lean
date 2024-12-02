/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Control.Option

namespace Lake

instance : Monad Task where
  map := Task.map
  pure := Task.pure
  bind := Task.bind

abbrev ETask ε := ExceptT ε Task
abbrev OptionTask := OptionT Task

def BaseIOTask := Task
instance : Monad BaseIOTask := inferInstanceAs <| Monad Task
instance [Inhabited α] : Inhabited (BaseIOTask α) := inferInstance

abbrev EIOTask ε := ExceptT ε BaseIOTask
abbrev OptionIOTask := OptionT BaseIOTask

instance : Inhabited (OptionIOTask α) := ⟨failure⟩
