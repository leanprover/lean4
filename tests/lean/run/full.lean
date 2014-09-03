import logic
namespace foo
  variable x : num.num
  check x
  open num
  check x
  set_option pp.full_names true
  check x
end foo
