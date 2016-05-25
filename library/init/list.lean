/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic
open decidable list

definition list.has_decidable_eq [instance] {A : Type} [H : decidable_eq A] (l₁ : list A) :  ∀ l₂ : list A, decidable (l₁ = l₂) :=
list.rec_on l₁
  (λ l₂, list.cases_on l₂
    (tt rfl)
    (λ b l₂, ff (λ H, list.no_confusion H)))
  (λ a l₁ ih l₂, list.cases_on l₂
    (ff (λ H, list.no_confusion H))
    (λ b l₂,
       decidable.cases_on (H a b)
        (λ Hnab : a ≠ b, ff (λ H, list.no_confusion H (λ Hab Hl₁l₂, absurd Hab Hnab)))
        (λ Hab : a = b,
           decidable.cases_on (ih l₂)
             (λ Hne : l₁ ≠ l₂, ff (λ H, list.no_confusion H (λ Hab Hl₁l₂, absurd Hl₁l₂ Hne)))
             (λ He  : l₁ = l₂, tt (congr (congr_arg cons Hab) He)))))
