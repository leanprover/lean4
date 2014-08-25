import logic

check
  let f x y := x ∧ y,
      g x   := f x x,
      a     := g true
  in  λ (x : a),
        let h x y := f x (g y),
            b     := h
        in b
