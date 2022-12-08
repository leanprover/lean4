def foo: List Unit → Type
| []       => Unit → Unit
| _ :: tl  => foo tl

partial def bar: (l: List Unit) → foo l → foo l
| []     , f => λ t => f t
| _ :: tl, f => bar tl f

def bar': (l: List Unit) → foo l → foo l
| []     , f => by simp only [foo] at f; exact (λ t => f t)
| _ :: tl, f => bar' tl f

#eval bar [()] id ()
