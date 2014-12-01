prelude
precedence `+`  : 65
precedence `++` : 100
constant N : Type.{1}
constant f : N → N → N
constant a : N
check
   let g x y         := f x y,
       infix +       := g,
       b : N         := a+a,
       c             := b+a,
       h (x : N)     := x+x,
       postfix ++    := h,
       d             := c++,
       r (x : N) : N := x++++
   in  f b (r c)
