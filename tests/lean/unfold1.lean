open tactic

meta definition rewriteH (Hname : name) : tactic unit :=
do get_local Hname >>= rewrite_core reducible tt tt occurrences.all ff,
   try reflexivity

example (l : list nat) : list.append l [] = l :=
by do
  get_local `l >>= λ H, induction H [`h, `t, `iH],
  --
  dunfold [`list.append],
  trace_state,
  trace "------",
  reflexivity,
  dunfold [`list.append],
  trace_state,
  rewriteH `iH
