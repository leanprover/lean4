module
import Lean.Elab.Command

theorem extracted_1_1 {K : Type} [Lean.Grind.Field K] (pB ppB pBf ifpnf : K) :
  ifpnf ≠ 0 →
    pBf + ppB = pB * (1 / ifpnf) + ppB →
      ifpnf / (ppB * ifpnf + pB) = 1 / (ppB + pBf)
  :=
  by grind -abstractProof only [cases Or]

theorem extracted_1_2 {K : Type} [Lean.Grind.Field K] (pB ppB pBf ifpnf : K) :
  ifpnf ≠ 0 →
    pBf + ppB = pB * (1 / ifpnf) + ppB →
      ifpnf / (ppB * ifpnf + pB) = 1 / (ppB + pBf)
  :=
  by grind -abstractProof only [cases Or]

theorem extracted_1_3 {K : Type} [Lean.Grind.Field K] (pB ppB pBf ifpnf : K) :
  ifpnf ≠ 0 →
    pBf + ppB = pB * (1 / ifpnf) + ppB →
      ifpnf / (ppB * ifpnf + pB) = 1 / (ppB + pBf)
  :=
  by grind -abstractProof only [cases Or]

theorem extracted_1_4 {K : Type} [Lean.Grind.Field K] (pB ppB pBf ifpnf : K) :
  ifpnf ≠ 0 →
    pBf + ppB = pB * (1 / ifpnf) + ppB →
      ifpnf / (ppB * ifpnf + pB) = 1 / (ppB + pBf)
  :=
  by grind -abstractProof only [cases Or]

theorem extracted_1_5 {K : Type} [Lean.Grind.Field K] (pB ppB pBf ifpnf : K) :
  ifpnf ≠ 0 →
    pBf + ppB = pB * (1 / ifpnf) + ppB →
      ifpnf / (ppB * ifpnf + pB) = 1 / (ppB + pBf)
  :=
  by grind -abstractProof only [cases Or]

theorem extracted_1_6 {K : Type} [Lean.Grind.Field K] (pB ppB pBf ifpnf : K) :
  ifpnf ≠ 0 →
    pBf + ppB = pB * (1 / ifpnf) + ppB →
      ifpnf / (ppB * ifpnf + pB) = 1 / (ppB + pBf)
  :=
  by grind -abstractProof only [cases Or]

open Lean
run_cmd
  let env ← getEnv
  let some (.thmInfo ci_1) := env.find? ``extracted_1_1 | unreachable!
  let some (.thmInfo ci_2) := env.find? ``extracted_1_2 | unreachable!
  let some (.thmInfo ci_3) := env.find? ``extracted_1_3 | unreachable!
  let some (.thmInfo ci_4) := env.find? ``extracted_1_4 | unreachable!
  let some (.thmInfo ci_5) := env.find? ``extracted_1_5 | unreachable!
  let some (.thmInfo ci_6) := env.find? ``extracted_1_6 | unreachable!
  assert! ci_1.value.hash == ci_2.value.hash
  assert! ci_1.value.hash == ci_3.value.hash
  assert! ci_1.value.hash == ci_4.value.hash
  assert! ci_1.value.hash == ci_5.value.hash
  assert! ci_1.value.hash == ci_6.value.hash
