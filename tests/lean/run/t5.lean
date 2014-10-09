constant N : Type.{1}
namespace foo
  constant N : Type.{2}
  namespace tst
    constant N : Type.{3}
    print raw N
  end tst
end foo
print raw N
namespace foo
  print raw N
  namespace tst
    print raw N N -> N
    section
      variable N : Type.{4} -- Shadow previous ones.
      print raw N
    end
  end tst
end  foo
