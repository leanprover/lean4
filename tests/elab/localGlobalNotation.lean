/-! `notation` should avoid name conflicts, also between local/global. -/
namespace Foo

local notation "foo" => 1
notation "foo" => 1
