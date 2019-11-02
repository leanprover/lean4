/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment

namespace Lean

def mkAuxRecursorExtension : IO TagDeclarationExtension :=
mkTagDeclarationExtension `auxRec

@[init mkAuxRecursorExtension]
constant auxRecExt : TagDeclarationExtension := default _

@[export lean_mark_aux_recursor]
def markAuxRecursor (env : Environment) (n : Name) : Environment :=
auxRecExt.tag env n

@[export lean_is_aux_recursor]
def isAuxRecursor (env : Environment) (n : Name) : Bool :=
auxRecExt.isTagged env n

def mkNoConfusionExtension : IO TagDeclarationExtension :=
mkTagDeclarationExtension `noConf

@[init mkNoConfusionExtension]
constant noConfusionExt : TagDeclarationExtension := default _

@[export lean_mark_no_confusion]
def markNoConfusion (env : Environment) (n : Name) : Environment :=
noConfusionExt.tag env n

@[export lean_is_no_confusion]
def isNoConfusion (env : Environment) (n : Name) : Bool :=
noConfusionExt.isTagged env n

end Lean
