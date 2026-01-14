example
  {p: Prop}
  (h: True → p)
  : p := by
  simp (discharger := skip) [h] -- simp made no progress

example
  {p: Prop}
  (h: True → p)
  : p := by
  simp (discharger := simp) [h]

example
  {p: Prop}
  (h: True → p)
  : p := by
  simp (discharger := trace "hello"; simp) [h]
