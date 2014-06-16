precedence `+`  : 65
precedence `++` : 100
variable N : Type.{1}
variable f : N → N → N
variable a : N
print raw
   let g x y         := f x y,
       infix +       := g,
       b : N         := a+a,
       c             := b+a,
       h (x : N)     := x+x,
       postfix ++    := h,
       d             := c++,
       r (x : N) : N := x++++
   in  f b (r c)
