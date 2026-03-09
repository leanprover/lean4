set_option cbv.warning false

example : ("abc".pos ⟨1⟩ (by decide_cbv)).get (by decide_cbv) = 'b' := by decide_cbv
