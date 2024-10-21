/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.LawfulOperator
import Std.Sat.AIG.CachedGatesLemmas

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α] {aig : AIG α}

namespace RefVec

def empty : RefVec aig 0 where
  refs := #[]
  hlen := by simp
  hrefs := by intros; contradiction

@[inline]
def cast' {aig1 aig2 : AIG α} (s : RefVec aig1 len)
    (h :
      (∀ {i : Nat} (h : i < len), s.refs[i]'(by have := s.hlen; omega) < aig1.decls.size)
        → ∀ {i : Nat} (h : i < len), s.refs[i]'(by have := s.hlen; omega) < aig2.decls.size) :
    RefVec aig2 len :=
  { s with
    hrefs := by
      intros
      apply h
      · intros
        apply s.hrefs
        assumption
      · assumption
  }

@[inline]
def cast {aig1 aig2 : AIG α} (s : RefVec aig1 len) (h : aig1.decls.size ≤ aig2.decls.size) :
    RefVec aig2 len :=
  s.cast' <| by
    intro hall i hi
    specialize hall hi
    omega

@[inline]
def get (s : RefVec aig len) (idx : Nat) (hidx : idx < len) : Ref aig :=
  let ⟨refs, hlen, hrefs⟩ := s
  let ref := refs[idx]'(by rw [hlen]; assumption)
  ⟨ref, by apply hrefs; assumption⟩

@[inline]
def push (s : RefVec aig len) (ref : AIG.Ref aig) : RefVec aig (len + 1) :=
  let ⟨refs, hlen, hrefs⟩ := s
  ⟨
    refs.push ref.gate,
    by simp [hlen],
    by
      intro i hi
      simp only [Array.getElem_push]
      split
      · apply hrefs
        omega
      · apply AIG.Ref.hgate
  ⟩

@[simp]
theorem get_push_ref_eq (s : RefVec aig len) (ref : AIG.Ref aig) :
    (s.push ref).get len (by omega) = ref := by
  have := s.hlen
  simp [get, push, ← this]

-- This variant exists because it is sometimes hard to rewrite properly with DTT.
theorem get_push_ref_eq' (s : RefVec aig len) (ref : AIG.Ref aig) (idx : Nat)
    (hidx : idx = len) :
    (s.push ref).get idx (by omega) = ref := by
  have := s.hlen
  simp [get, push, ← this, hidx]

theorem get_push_ref_lt (s : RefVec aig len) (ref : AIG.Ref aig) (idx : Nat)
    (hidx : idx < len) :
    (s.push ref).get idx (by omega) = s.get idx hidx := by
  simp only [get, push, Ref.mk.injEq]
  cases ref
  simp only [Ref.mk.injEq]
  rw [Array.getElem_push_lt]

@[simp]
theorem get_cast {aig1 aig2 : AIG α} (s : RefVec aig1 len) (idx : Nat) (hidx : idx < len)
    (hcast : aig1.decls.size ≤ aig2.decls.size) :
    (s.cast hcast).get idx hidx
      =
    (s.get idx hidx).cast hcast := by
  simp [cast, cast', get]

@[inline]
def append (lhs : RefVec aig lw) (rhs : RefVec aig rw) : RefVec aig (lw + rw) :=
  let ⟨lrefs, hl1, hl2⟩ := lhs
  let ⟨rrefs, hr1, hr2⟩ := rhs
  ⟨
    lrefs ++ rrefs,
    by simp [Array.size_append, hl1, hr1],
    by
      intro i h
      by_cases hsplit : i < lrefs.size
      · rw [Array.getElem_append_left]
        apply hl2
        omega
      · rw [Array.getElem_append_right]
        · apply hr2
          omega
        · omega
  ⟩

theorem get_append (lhs : RefVec aig lw) (rhs : RefVec aig rw) (idx : Nat)
    (hidx : idx < lw + rw) :
    (lhs.append rhs).get idx hidx
      =
    if h : idx < lw then
      lhs.get idx h
    else
      rhs.get (idx - lw) (by omega) := by
  simp only [get, append]
  split
  · simp [Ref.mk.injEq]
    rw [Array.getElem_append_left]
  · simp only [Ref.mk.injEq]
    rw [Array.getElem_append_right]
    · simp [lhs.hlen]
    · rw [lhs.hlen]
      omega

@[inline]
def getD (s : RefVec aig len) (idx : Nat) (alt : Ref aig) : Ref aig :=
  if hidx : idx < len then
    s.get idx hidx
  else
    alt

theorem get_in_bound (s : RefVec aig len) (idx : Nat) (alt : Ref aig) (hidx : idx < len) :
    s.getD idx alt = s.get idx hidx := by
  unfold getD
  simp [hidx]

theorem get_out_bound (s : RefVec aig len) (idx : Nat) (alt : Ref aig) (hidx : len ≤ idx) :
    s.getD idx alt = alt := by
  unfold getD
  split
  · omega
  · rfl

def countKnown [Inhabited α] (aig : AIG α) (s : RefVec aig len) : Nat := Id.run do
  let folder acc ref :=
    let decl := aig.decls[ref]!
    match decl with
    | .const .. => acc + 1
    | _ => acc
  return s.refs.foldl (init := 0) folder

end RefVec

structure BinaryRefVec (aig : AIG α) (len : Nat) where
  lhs : RefVec aig len
  rhs : RefVec aig len

namespace BinaryRefVec

@[inline]
def cast {aig1 aig2 : AIG α} (s : BinaryRefVec aig1 len)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    BinaryRefVec aig2 len :=
  let ⟨lhs, rhs⟩ := s
  ⟨lhs.cast h, rhs.cast h⟩

@[simp]
theorem lhs_get_cast {aig1 aig2 : AIG α} (s : BinaryRefVec aig1 len) (idx : Nat)
    (hidx : idx < len) (hcast : aig1.decls.size ≤ aig2.decls.size) :
    (s.cast hcast).lhs.get idx hidx
      =
    (s.lhs.get idx hidx).cast hcast := by
  simp [cast]

@[simp]
theorem rhs_get_cast {aig1 aig2 : AIG α} (s : BinaryRefVec aig1 len) (idx : Nat)
    (hidx : idx < len) (hcast : aig1.decls.size ≤ aig2.decls.size) :
    (s.cast hcast).rhs.get idx hidx
      =
    (s.rhs.get idx hidx).cast hcast := by
  simp [cast]

end BinaryRefVec
end AIG

end Sat
end Std
