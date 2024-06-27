/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Unicode.Unicode

def referenceTable (ucd : List UnicodeData) (property : UnicodeData → Bool) : List Nat :=
  (ucd.filter property).map (fun ucdc => ucdc.codepoint)

def referenceSearch (table : List Nat) (c : Char) : Bool :=
  table.contains c.toNat

@[simp]
noncomputable def reference (ucd : List UnicodeData) (property : UnicodeData → Bool) (c : Char) : Bool :=
  let table := referenceTable ucd property
  referenceSearch table c
