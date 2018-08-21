import init.lean.trace

namespace lean
namespace trace

meta def test (opts : options) : id trace_map :=
prod.snd <$> trace_t.run opts (
trace_root ⟨1, 0⟩ `trace.type_context.is_def_eq "type_context.is_def_eq trace" ⟨λ _,
  trace_ctx `trace.type_context.is_def_eq "f 0 =?= f a (approximate mode)" ⟨λ _,
    trace_ctx `trace.type_context.is_def_eq_detail "f 0 =?= f a" ⟨λ _,
      trace `trace.type_context.is_def_eq_detail "0 =?= a" >>
      trace `trace.type_context.is_def_eq_detail "...failed"
    ⟩ >>
    trace `trace.type_context.is_def_eq "...failed"
  ⟩
⟩)

run_cmd
do let test opts := tactic.trace $ format.join $ list.intersperse format.line $ (test opts).to_list.map $ λ ⟨pos, tr⟩, to_fmt pos ++ ": " ++ tr.pp,
   test options.mk,
   tactic.trace "---",
   let opts := options.mk.set_bool `trace.type_context.is_def_eq tt,
   test opts,
   tactic.trace "---",
   test (opts.set_bool `trace.type_context.is_def_eq_detail tt),
   tactic.trace "---",
   test (opts.set_bool `trace.type_context.is_def_eq ff)

end trace
end lean
