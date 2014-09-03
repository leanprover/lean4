import logic

namespace foo
namespace boo
theorem tst : true := trivial
end boo
end foo

open foo
check boo.tst
