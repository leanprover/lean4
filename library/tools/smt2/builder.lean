import .syntax

@[reducible] def smt2.builder (α : Type) := state (list smt2.cmd) α

meta def smt2.builder.to_format {α : Type} (build : smt2.builder α) : format :=
format.join $ list.map to_fmt $ (build []).snd

meta instance (α : Type) : has_to_format (smt2.builder α) :=
⟨ smt2.builder.to_format ⟩

namespace smt2

namespace builder

def add_command (c : cmd) : builder unit := do
cs ← state.read,
state.write (c :: cs)

def echo (msg : string) : builder unit :=
add_command (cmd.echo msg)

def check_sat : builder unit :=
add_command cmd.check_sat

def pop (n : nat) : builder unit :=
add_command $ cmd.pop n

def push (n : nat) : builder unit :=
add_command $ cmd.push n

def scope {α} (level : nat) (action : builder α) : builder α :=
do push level,
   res ← action,
   pop level,
   return res

def reset : builder unit :=
add_command cmd.reset

def exit' : builder unit :=
add_command cmd.exit_cmd

def declare_const (sym : string) (s : sort) : builder unit :=
add_command $ cmd.declare_const sym s

end builder

end smt2
