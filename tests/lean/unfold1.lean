open tactic

meta definition rewriteH (Hname : name) : tactic unit :=
do do h ← get_local Hname,
   rewrite_target h,
   try reflexivity

example (l : list nat) : list.append l [] = l :=
by do
  get_local `l >>= λ H, induction H [`h, `t, `iH],
  --
  dunfold_target [`list.append],
  trace_state,
  trace "------",
  reflexivity,
  dunfold_target [`list.append],
  trace_state,
  rewriteH `iH
