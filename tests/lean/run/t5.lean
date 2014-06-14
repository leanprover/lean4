variable N : Type.{1}
namespace foo
  variable N : Type.{2}
  namespace tst
    variable N : Type.{3}
    print raw N
  end
end
print raw N
namespace foo
  print raw N
  namespace tst
    print raw N N -> N
    section
      variable N : Type.{4} -- Shadow previous ones.
      print raw N
    end
  end
end