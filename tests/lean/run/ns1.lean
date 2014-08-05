import standard

namespace foo
namespace boo
theorem tst : true := trivial
end
end

using foo
check boo.tst