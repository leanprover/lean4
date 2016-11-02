open tactic

def g : nat → nat :=
λ n, 0

meta def show_pos (n : name) : command :=
do env   ← get_env,
   pos   ← returnopt (env^.decl_pos_info n),
   olean ← returnopt (env^.decl_olean n) <|> return "current file",
   trace $ to_string n ++ " was defined at " ++ olean ++ " : " ++ to_string pos

run_command show_pos `add
run_command show_pos `nat.succ
run_command show_pos `subsingleton.intro
run_command show_pos `subsingleton.rec
run_command show_pos `nat.add
run_command show_pos `quot
run_command show_pos `g
