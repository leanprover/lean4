/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Prelude

public section

namespace Lean

@[extern "lean_closure_max_args"]
opaque closureMaxArgsFn : Unit → Nat

@[extern "lean_max_small_nat"]
opaque maxSmallNatFn : Unit → Nat

@[extern "lean_get_max_ctor_fields"]
opaque getMaxCtorFields : Unit → Nat
def maxCtorFields := getMaxCtorFields ()

@[extern "lean_get_max_ctor_scalars_size"]
opaque getMaxCtorScalarsSize : Unit → Nat
def maxCtorScalarsSize := getMaxCtorScalarsSize ()

@[extern "lean_get_max_ctor_tag"]
opaque getMaxCtorTag : Unit → Nat
def maxCtorTag := getMaxCtorTag ()

@[extern "lean_get_usize_size"]
opaque getUSizeSize : Unit → Nat
def usizeSize := getUSizeSize ()


@[extern "lean_libuv_version"]
opaque libUVVersionFn : Unit → Nat

@[extern "lean_openssl_version"]
opaque openSSLVersionFn : Unit → Nat

def closureMaxArgs : Nat :=
  closureMaxArgsFn ()

def maxSmallNat : Nat :=
  maxSmallNatFn ()

def libUVVersion : Nat :=
  libUVVersionFn ()

def openSSLVersion : Nat :=
  openSSLVersionFn ()

end Lean
