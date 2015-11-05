/- Basic rewriting with iff with congr_iff -/
import logic.connectives
open nat
#simplify iff 2 (@le nat nat_has_le 0 0) -- true
#simplify iff 2 (@le nat nat_has_le 0 1) -- true
#simplify iff 2 (@le nat nat_has_le 0 2) -- true
#simplify iff 2 (@lt nat nat_has_lt 0 0) -- false
#simplify iff 2 (@lt nat nat_has_lt 0 (succ 0)) -- true
#simplify iff 2 (@lt nat nat_has_lt 1 (succ 1)) -- true
#simplify iff 2 (@lt nat nat_has_lt 0 (succ (succ 0))) -- true
#simplify iff 2 (@le nat nat_has_le 0 0 ↔ @le nat nat_has_le 0 0) -- true
#simplify iff 2 (@le nat nat_has_le 0 0 ↔ @le nat nat_has_le 0 1) -- true
#simplify iff 2 (@le nat nat_has_le 0 0 ↔ @lt nat nat_has_lt 0 0) -- false
