/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.GetElem
public import Init.Classical

public section

@[inherit_doc GetElem]
class GetElemV (coll : Type u) (idx : Type v) (elem : outParam (Type w)) where
  /--
  The syntax `arr[i]ᵛ` gets the `i`'th element of the collection `arr`,
  if it is present, and otherwise returns a (noncomputable) default value.
  -/
  getElemV [Nonempty elem] : coll → idx → elem

export GetElemV (getElemV)

/--
The syntax `arr[i]ᵛ` gets the `i`'th element of the collection `arr` or
a (noncomputable) default value if `i` is out of bounds.
-/
macro:max x:term noWs "[" i:term "]ᵛ" : term => `(getElemV $x $i)

recommended_spelling "getElemV" for "xs[i]ᵛ" in [GetElemV.getElemV, «term__[_]ᵛ»]

open Classical

noncomputable instance (priority := low) [GetElem coll idx elem valid] : GetElemV coll idx elem where
  getElemV xs i := if h : valid xs i then xs[i]'h else choice ‹Nonempty elem›

class LawfulGetElemV (cont : Type u) (idx : Type v) (elem : outParam (Type w))
   (dom : outParam (cont → idx → Prop)) [GetElem cont idx elem dom] [GetElemV cont idx elem] : Prop where
  /-- The "verification only" getter notation `xs[i]ᵛ` coincides with the usual `xs[i]`. -/
  getElemV_def [Nonempty elem] (c : cont) (i : idx) :
      c[i]ᵛ = if h : dom c i then c[i]'h else choice ‹Nonempty elem›

theorem getElem_eq_getElemV
    [GetElem coll idx elem valid] [GetElemV coll idx elem]
    [LawfulGetElemV coll idx elem valid] {xs : coll} {i : idx} (h : valid xs i) :
    xs[i] = @GetElemV.getElemV _ _ _ _ ⟨xs[i]⟩ xs i := by
  have : Nonempty elem := ⟨xs[i]⟩
  rw [LawfulGetElemV.getElemV_def, dif_pos h]
