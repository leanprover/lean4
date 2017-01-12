/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause_ops .prover_state
open expr tactic monad

namespace super

meta def try_assumption_lookup_left (c : clause) : tactic (list clause) :=
on_first_left c $ λtype, do
  ass ← find_assumption type,
  return [([], ass)]

meta def try_nonempty_lookup_left (c : clause) : tactic (list clause) :=
on_first_left_dn c $ λhnx,
  match is_local_not c^.local_false hnx^.local_type with
  | some type := do
    univ ← infer_univ type,
    lf_univ ← infer_univ c^.local_false,
    guard $ lf_univ = level.zero,
    inst ← mk_instance (app (const ``nonempty [univ]) type),
    instt ← infer_type inst,
    return [([], app_of_list (const ``nonempty.elim [univ])
                             [type, c^.local_false, inst, hnx])]
  | _ := failed
  end

meta def try_nonempty_left (c : clause) : tactic (list clause) :=
on_first_left c $ λprop,
  match prop with
  | (app (const ``nonempty [u]) type) := do
    x ← mk_local_def `x type,
    return [([x], app_of_list (const ``nonempty.intro [u]) [type, x])]
  | _ := failed
  end

meta def try_nonempty_right (c : clause) : tactic (list clause) :=
on_first_right c $ λhnonempty,
  match hnonempty^.local_type with
  | (app (const ``nonempty [u]) type) := do
    lf_univ ← infer_univ c^.local_false,
    guard $ lf_univ = level.zero,
    hnx ← mk_local_def `nx (imp type c^.local_false),
    return [([hnx], app_of_list (const ``nonempty.elim [u])
                                [type, c^.local_false, hnonempty, hnx])]
  | _ := failed
  end

meta def try_inhabited_left (c : clause) : tactic (list clause) :=
on_first_left c $ λprop,
  match prop with
  | (app (const ``inhabited [u]) type) := do
    x ← mk_local_def `x type,
    return [([x], app_of_list (const ``inhabited.mk [u]) [type, x])]
  | _ := failed
  end

meta def try_inhabited_right (c : clause) : tactic (list clause) :=
on_first_right' c $ λhinh,
  match hinh^.local_type with
  | (app (const ``inhabited [u]) type) :=
    return [([], app_of_list (const ``inhabited.default [u]) [type, hinh])]
  | _ := failed
  end

@[super.inf]
meta def inhabited_infs : inf_decl := inf_decl.mk 10 $ take given, do
for' [try_assumption_lookup_left,
      try_nonempty_lookup_left,
      try_nonempty_left, try_nonempty_right,
      try_inhabited_left, try_inhabited_right] $ λr,
      simp_if_successful given (r given^.c)

end super
