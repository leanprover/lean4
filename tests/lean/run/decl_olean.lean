open tactic

def g : nat → nat :=
λ n, 0

meta def show_pos (n : name) : command :=
do env   ← get_env,
   pos   ← returnopt (env^.decl_pos n),
   olean ← returnopt (env^.decl_olean n) <|> return "current file",
   trace $ to_string n ++ " was defined at " ++ olean ++ " : " ++ to_string pos.1 ++ ":" ++ to_string pos.2

run_command show_pos `add
run_command show_pos `nat.succ
run_command show_pos `subsingleton.intro
run_command show_pos `subsingleton.rec
run_command show_pos `nat.add
run_command show_pos `quotient
run_command show_pos `g
