open tactic

run_cmd
do let e := pexpr.mk_structure_instance { struct := some "prod", field_names := ["fst", "snd"], field_values := [``(1), ``(2)] },
   let f := pexpr.mk_structure_instance { field_names := ["snd"], field_values := [``(1)], sources := [e] },
   to_expr e >>= trace,
   to_expr f >>= trace,
   trace $ e.get_structure_instance_info >>= structure_instance_info.struct,
   trace $ f.get_structure_instance_info >>= structure_instance_info.struct
