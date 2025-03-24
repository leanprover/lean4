/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap
import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.DTreeMap
import Std.Data.TreeMap
import Std.Data.TreeSet

-- The three imports above only import the modules needed to work with the version which bundles
-- the well-formedness invariant, so we need to additionally import the files that deal with the
-- unbundled version
import Std.Data.DHashMap.RawLemmas
import Std.Data.HashMap.RawLemmas
import Std.Data.HashSet.RawLemmas
