import system.io
import data.buffer

meta def main : tactic unit := do
opts ← tactic.get_options,
let buf := format.to_buffer (format.of_string "foobar") opts,
tactic.trace buf

run_cmd main
