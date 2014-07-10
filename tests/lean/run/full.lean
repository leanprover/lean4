import standard
namespace foo
  variable x : num.num
  check x
  using num
  check x
  set_option pp.full_names true
  check x
end