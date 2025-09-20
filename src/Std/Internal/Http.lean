/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data
public import Std.Internal.Http.Server

public section

namespace Std
namespace Http

set_option linter.all true

/-!
# Http

It's a "low level" HTTP 1.1 implementation for LEAN. It is designed to be used with or without the
`Async` library if you want to implement a custom `Connection`.

# Overview

This module of the standard library defines a lot of concepts related to HTTP protocol
and the semantics in a Sans/IO format.

-/
