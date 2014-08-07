import standard

namespace foo
namespace boo
theorem tst : true := trivial
end boo
end foo

using foo
check boo.tst