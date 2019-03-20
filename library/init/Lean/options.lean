/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.lean.kvmap
universe u

namespace Lean

def Options := Kvmap

def Options.mk : Options :=
{Kvmap .}

end Lean
