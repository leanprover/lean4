module

prelude
import all Init.Data.BitVec.Basic

import Init.Grind

namespace BitVec

theorem getMsb_eq_getLsb (x : BitVec w) (i : Fin w) :
    x.getMsb i = x.getLsb ⟨w - 1 - i, by omega⟩ := by
  simp only [getMsb, getLsb]

theorem getMsb?_eq_getLsb? (x : BitVec w) (i : Nat) :
    x.getMsb? i = if i < w then x.getLsb? (w - 1 - i) else none := by
  simp only [getMsb?, getLsb?_eq_getElem?]
  split <;> grind [getMsb_eq_getLsb]
