/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean

builtin_initialize auxRecExt : TagDeclarationExtension ← mkTagDeclarationExtension `auxRec

@[export lean_mark_aux_recursor]
def markAuxRecursor (env : Environment) (n : Name) : Environment :=
auxRecExt.tag env n

@[export lean_is_aux_recursor]
def isAuxRecursor (env : Environment) (n : Name) : Bool :=
auxRecExt.isTagged env n

builtin_initialize noConfusionExt : TagDeclarationExtension ← mkTagDeclarationExtension `noConf

@[export lean_mark_no_confusion]
def markNoConfusion (env : Environment) (n : Name) : Environment :=
noConfusionExt.tag env n

@[export lean_is_no_confusion]
def isNoConfusion (env : Environment) (n : Name) : Bool :=
noConfusionExt.isTagged env n

end Lean
