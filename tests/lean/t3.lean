universe u
print raw Type.{u}
namespace tst
  universe v
  print raw Type.{v}
  print raw Type.{tst.v}
end tst
print raw Type.{tst.v}
print raw Type.{v}  -- Error: alias 'v' is not available anymore
section
  universe variable z -- Remark: this is a local universe
  print raw Type.{z}
end
print raw Type.{z}  -- Error: local universe 'z' is gone
section
  namespace foo -- Error: we cannot create a namespace inside a section
end
namespace tst
  print raw Type.{v} -- Remark: alias 'v' is available again
  print raw Type.{u}
  namespace foo
    universe U
  end foo
end tst
print raw Type.{tst.foo.U}
namespace tst.foo    -- Error: we cannot use qualified names in declarations
universe full.name.U -- Error: we cannot use qualified names in declarations
namespace tst
  namespace foo
    print raw Type.{v}  -- Remark: alias 'v' for 'tst.v' is available again
    print raw Type.{U}  -- Remark: alias 'U' for 'tst.foo.U' is available again
  end foo
end tst
namespace bla
  universe u -- Error: we cannot shadow universe levels
end bla
print raw Type.{bla.u} -- Error: we failed to declare bla.u
