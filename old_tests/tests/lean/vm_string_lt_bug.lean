open native

#eval to_bool ("a" < "b")
#eval to_bool ("b" < "b")

namespace test1
meta def m := rb_map.mk string nat

meta def m' := m.insert "foo" 10

#eval m'.find "foo"
end test1

namespace test2

meta def m := rb_map.mk nat nat

meta def m' := m.insert 3 10

#eval m'.find 3

end test2
