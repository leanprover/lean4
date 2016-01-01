/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/strategy.h"

namespace lean {
namespace blast {
/*
Auxiliary strategy for applying recursors automatically.
The idea is to simulate the case-analysis used in many theorems
in the standard library.

Example:

theorem last_concat [simp] {x : T} : ∀ {l : list T} (h : concat x l ≠ []), last (concat x l) h = x
| []          h := rfl
| [a]         h := rfl
| (a₁::a₂::l) h :=
  begin
    change last (a₁::a₂::concat x l) !cons_ne_nil = x,
    rewrite last_cons_cons,
    change last (concat x (a₂::l)) !concat_ne_nil = x,
    apply last_concat
  end


Options:
1) ignore non-recursive     (true)
2) ignore type classes      (true)
3) ignore structures        (true)
4) maximum number of rounds 3

Each is an iterative deepening procedure.
*/

/* Procedure for retrieving hypotheses from the current state.
   The rec_and_then strategy will apply the recursor action on the candidates.
   Actually, it creates a choice point for trying each candidate. */
typedef std::function<void(hypothesis_idx_buffer &)> rec_candidate_selector;

strategy rec_and_then(strategy const & S, rec_candidate_selector const & selector);

/* Use default selector */
strategy rec_and_then(strategy const & S);

void initialize_recursor_strategy();
void finalize_recursor_strategy();
}}
