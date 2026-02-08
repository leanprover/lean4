/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Control.Option
public import Init.Control.Except

namespace Lake

public instance : Monad Task where
  map := Task.map
  pure := Task.pure
  bind := Task.bind

public abbrev ETask ε := ExceptT ε Task
public abbrev OptionTask := OptionT Task

@[expose] public def BaseIOTask := Task
public instance : Monad BaseIOTask := inferInstanceAs (Monad Task)
public instance [Inhabited α] : Inhabited (BaseIOTask α) := inferInstance

public abbrev EIOTask ε := ExceptT ε BaseIOTask
public abbrev OptionIOTask := OptionT BaseIOTask

public instance : Inhabited (OptionIOTask α) := ⟨failure⟩
