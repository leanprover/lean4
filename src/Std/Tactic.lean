/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide

/-!
This directory is mainly used for bootstrapping reasons. Suppose a tactic generates a proof term
that contains either directly things from `Std` or custom lemmas/definitions that make use of
things from `Std`. These lemmas/definitions could not be put into `Init` for dependency reasons but
storing them in `Lean` directly is also not perfect because we do not want end users to import the
compiler. This directory offers a place for such definitions to live, such that the user only has
to import `Std.Tactic` to use such a tactic.

Note that this does not contain meta programs that implement tactics themselves because these would
rely on importing things from `Lean` which cannot done in `Std`.
-/
