import system.io

open tactic

meta def get_decl_names_with_prefix (p : name) : tactic (list name) :=
do env ← get_env,
   return $ env.fold [] $ λ d r,
     let n := d.to_name in
     if p.is_prefix_of n then n :: r else r

meta def main : io unit :=
do io.put_str "Declarations with prefix 'nat'\n",
   ns ← io.run_tactic (get_decl_names_with_prefix `nat),
   ns.mmap' $ λ n, io.put_str_ln $ to_string n,
   return ()
