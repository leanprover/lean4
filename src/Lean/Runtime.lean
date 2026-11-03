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

@[extern "lean_get_max_ctor_num_objs"]
opaque getMaxCtorNumObjs : Unit → Nat
def maxCtorNumObjs := getMaxCtorNumObjs ()

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

/-- A SHA-256 digest as its big-endian 64-bit words (i.e., `w0` holds its first eight bytes). -/
structure Internal.Sha256Digest where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64

/-- Returns the SHA-256 digest of `bytes`. -/
@[extern "lean_sha256"]
opaque Internal.sha256 (bytes : @& ByteArray) : Internal.Sha256Digest := ⟨default, default, default, default⟩

/-- Returns the SHA-256 digest of the UTF-8 encoding of `s`. -/
@[extern "lean_sha256_string"]
opaque Internal.sha256String (s : @& String) : Internal.Sha256Digest := ⟨default, default, default, default⟩

/-- Returns the SHA-256 digest of the concatenation of the digests `a` and `b`. -/
@[extern "lean_sha256_mix"]
opaque Internal.sha256Mix (a b : @& Internal.Sha256Digest) : Internal.Sha256Digest := ⟨default, default, default, default⟩

end Lean
