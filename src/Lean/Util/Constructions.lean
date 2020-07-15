/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean

@[extern "lean_mk_cases_on"] constant mkCasesOn (env : Environment) (name : @& Name) : Environment := env
@[extern "lean_mk_rec_on"] constant mkRecOn (env : Environment) (name : @& Name) : Environment := env
@[extern "lean_mk_no_confusion"] constant mkNoConfusion (env : Environment) (name : @& Name) : Environment := env
@[extern "lean_mk_below"] constant mkBelow (env : Environment) (name : @& Name) : Environment := env
@[extern "lean_mk_ibelow"] constant mkIBelow (env : Environment) (name : @& Name) : Environment := env
@[extern "lean_mk_brec_on"] constant mkBRecOn (env : Environment) (name : @& Name) : Environment := env
@[extern "lean_mk_binduction_on"] constant mkBInductionOn (env : Environment) (name : @& Name) : Environment := env

end Lean
