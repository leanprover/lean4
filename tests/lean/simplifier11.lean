-- Conditional congruence
import logic.connectives logic.quantifiers

namespace if_congr
constants {A : Type} {b c : Prop} (dec_b : decidable b) (dec_c : decidable c)
          {x y u v : A} (h_c : b ↔ c) (h_t : x = u) (h_e : y = v)

local attribute dec_b [instance]
local attribute dec_c [instance]
local attribute h_c [simp]
local attribute h_t [simp]
local attribute h_e [simp]

attribute if_congr [congr]

#simplify eq 0 (ite b x y)
end if_congr

namespace if_ctx_simp_congr
constants {A : Type} {b c : Prop} (dec_b : decidable b)
          {x y u v : A} (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v)

local attribute dec_b [instance]
local attribute h_c [simp]
local attribute h_t [simp]
local attribute h_e [simp]

attribute if_ctx_simp_congr [congr]

#simplify eq 0 (ite b x y)

end if_ctx_simp_congr

namespace if_congr_prop
constants {b c x y u v : Prop} (dec_b : decidable b) (dec_c : decidable c)
          (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v))

local attribute dec_b [instance]
local attribute dec_c [instance]
local attribute h_c [simp]
local attribute h_t [simp]
local attribute h_e [simp]

attribute if_congr_prop [congr]

#simplify iff 0 (ite b x y)
end if_congr_prop

namespace if_ctx_simp_congr_prop
constants (b c x y u v : Prop) (dec_b : decidable b)
          (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬ c → (y ↔ v))

local attribute dec_b [instance]
local attribute h_c [simp]
local attribute h_t [simp]
local attribute h_e [simp]

attribute if_ctx_simp_congr_prop [congr]
#simplify iff 0 (ite b x y)

end if_ctx_simp_congr_prop

namespace if_simp_congr_prop
constants (b c x y u v : Prop) (dec_b : decidable b)
          (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v)

local attribute dec_b [instance]
local attribute h_c [simp]
local attribute h_t [simp]
local attribute h_e [simp]

attribute if_simp_congr_prop [congr]
#simplify iff 0 (ite b x y)
end if_simp_congr_prop
