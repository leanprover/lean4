/- Basic rewriting with iff with congr_iff -/
import logic.connectives
open nat
namespace tst
attribute iff_self true_iff_false self_lt_succ_iff_true zero_lt_succ_iff_true zero_le_iff_true succ_le_self_iff_false succ_le_self_iff_false lt_self_iff_false [simp]
end tst
#simplify iff tst 2 (@le nat nat_has_le 0 0) -- true
#simplify iff tst 2 (@le nat nat_has_le 0 1) -- true
#simplify iff tst 2 (@le nat nat_has_le 0 2) -- true
#simplify iff tst 2 (@lt nat nat_has_lt 0 0) -- false
#simplify iff tst 2 (@lt nat nat_has_lt 0 (succ 0)) -- true
#simplify iff tst 2 (@lt nat nat_has_lt 1 (succ 1)) -- true
#simplify iff tst 2 (@lt nat nat_has_lt 0 (succ (succ 0))) -- true
#simplify iff tst 2 (@le nat nat_has_le 0 0 ↔ @le nat nat_has_le 0 0) -- true
#simplify iff tst 2 (@le nat nat_has_le 0 0 ↔ @le nat nat_has_le 0 1) -- true
#simplify iff tst 2 (@le nat nat_has_le 0 0 ↔ @lt nat nat_has_lt 0 0) -- false
