exit -- TODO(Leo): enable test again after we add rfl lemma support to type_context
open tactic

meta definition rewriteH (Hname : name) : tactic unit :=
do get_local Hname >>= rewrite_core reducible tt occurrences.all ff,
   try reflexivity

example (l : list nat) : list.append l [] = l :=
by do
  get_local `l >>= λ H, induction_core semireducible H `list.rec_on [`h, `t, `iH],
  --
  unfold [`list.append],
  trace_state,
  trace "------",
  reflexivity,
  unfold [`list.append],
  trace_state,
  rewriteH `iH
