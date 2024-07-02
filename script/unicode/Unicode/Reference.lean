/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Unicode.Unicode

def referenceTable (ucd : Array UnicodeData) (property : UnicodeData → Bool) : Array Nat :=
  (ucd.filter property).map fun ucdc => ucdc.codepoint

def referenceSearch (table : Array Nat) (c : Char) : Bool :=
  table.contains c.toNat
