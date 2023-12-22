example {p : Prop} (h : True → p) : p := by
  -- Prior to #2640, the failure of the discharger here would result in an error being reported to the user
  -- (rather than just `simp` making no progress).
  -- Now we use `withoutModifyingState` rather than `withoutModifyingStateWithInfoAndMessages` when invoking the discharger.
  simp (discharger := skip) [h]
