/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Internal.Http.Util.Buffer
public import Std.Internal.Http.Data.Version

public section

namespace Std
namespace Http

open Util

set_option linter.all true

/--
Serializes a type `t` to a `Buffer` containing its canonical HTTP representation
for protocol version `v`.
-/
class Encode (v : Version) (t : Type) where

  /--
  Encodes a type `t` to a `Buffer`.
  -/
  encode : Buffer → t → Buffer

instance : Encode .v11 Version where
  encode buffer := buffer.writeString ∘ toString
