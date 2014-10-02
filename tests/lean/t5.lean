constant N : Type.{1}
constant f : N → N
constant a : N
definition g (a : N) : N := f a
check g
namespace foo
  definition h : N := f a
  check h
  private definition q : N := f a
  check q
end foo
check foo.h
check q -- Error q is now hidden
