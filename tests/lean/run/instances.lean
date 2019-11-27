import Init.Lean
open Lean
open Lean.Meta

def tst1 : IO Unit :=
do let mods := [`Init.Lean];
   env ← importModules $ mods.map $ fun m => {module := m};
   let insts := getInstances env;
   IO.println (format insts);
   pure ()

#eval tst1
