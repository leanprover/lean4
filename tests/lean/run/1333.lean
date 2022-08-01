example
  (h1 : a = b + 3)
  (h2 : b = c + 2)
  (h3 : c = d + 1)
  (h4 : d = e + 4)
  (useless : a = x + 1)
  (H : a = 10) :
  e = 0 := by
  simp [*, -useless] at H
  exact H

example
  (useless : a = x + 1)
  (h1 : a = b + 3)
  (h2 : b = c + 2)
  (h3 : c = d + 1)
  (h4 : d = e + 4)
  (H : a = 10) :
  e = 0 := by
  simp [*, -useless] at H
  exact H

example
  (useless : a = x + 1)
  (h1 : a = b + 3)
  (h2 : b = c + 2)
  (h3 : c = d + 1)
  (h4 : d = e + 4)
  (H : a = 10) :
  e = 0 := by
  simp [*] at H
  rw [H] at useless
  simp [*, -H] at useless
  exact useless
