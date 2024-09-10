/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Attributes

/-!
# Attributes for the pretty printer

This module defines attributes that influence pretty printer output.
-/

namespace Lean

builtin_initialize ppUsingAnonymousConstructorAttr : TagAttribute ←
  registerTagAttribute `pp_using_anonymous_constructor "mark structure to be pretty printed using `⟨a,b,c⟩` notation"

builtin_initialize ppNoDotAttr : TagAttribute ←
  registerTagAttribute `pp_nodot "mark declaration to never be pretty printed using field notation"

/--
Returns whether or not the given declaration has the `@[pp_using_anonymous_constructor]` attribute.
-/
def hasPPUsingAnonymousConstructorAttribute (env : Environment) (declName : Name) : Bool :=
  ppUsingAnonymousConstructorAttr.hasTag env declName

/--
Returns whether or not the given declaration has the `@[pp_nodot]` attribute.
-/
def hasPPNoDotAttribute (env : Environment) (declName : Name) : Bool :=
  ppNoDotAttr.hasTag env declName

end Lean
