section tst1
open nat
#check succ
hide succ
#check succ -- Error
end tst1

section tst2
open nat
hide succ
def succ := tt
#check succ -- Should not fail, it is not ambiguous since the alias nat.succ has been hidden
end tst2

section tst3
open nat
section nested
hide zero
#check zero -- Error
end nested
#check zero -- Should work, the scope of the previous `hide` is the section nested
end tst3

namespace tst4
open nat
namespace nested
hide zero
#check zero -- Error
end nested
#check zero -- Should work, the scope of the previous `hide` is the namespace nested
end tst4

section tst5
hide nat.succ -- Error, we can only hide aliases for now
end tst5

section tst6
#check @is_true -- is_true is an alias for decidable.is_true
hide is_true
#check @is_true -- Error
end tst6
#check @is_true

def is_true := tt
#check is_true -- Error, is_true is now ambiguous
hide is_true
#check is_true -- should work, is_true : bool

section tst7
open list
#check map
#check foldl
hide map foldl
#check map -- Error
#check foldl -- Error
end tst7
