/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude

namespace Std
namespace Internal
namespace Http

/-!
# Http

The lean API for Http.

# Overview

This module of the standard library defines a lot of concepts related to HTTP protocol
and the semantics in a Sans/IO format.

# Http 1.1

It's made mainly for Http 1.1 using https://httpwg.org/specs/rfc9112.html as the main
recomendation.

-/
