-- Conditional congruence
import logic.connectives logic.quantifiers

-- TODO(dhs): add this to the library
lemma not_false_true [simp] : (¬ false) ↔ true := sorry

namespace if_congr
constants {A : Type} {b c : Prop} (dec_b : decidable b) (dec_c : decidable c)
          {x y u v : A} (h_c : b ↔ c) (h_t : x = u) (h_e : y = v)

attribute dec_b [instance]
attribute dec_c [instance]
attribute h_c [simp]
attribute h_t [simp]
attribute h_e [simp]

attribute if_congr [congr]

#simplify eq env 0 (ite b x y)
end if_congr

namespace if_ctx_simp_congr
constants {A : Type} {b c : Prop} (dec_b : decidable b)
          {x y u v : A} (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v)

attribute dec_b [instance]
attribute h_c [simp]
attribute h_t [simp]
attribute h_e [simp]

attribute if_ctx_simp_congr [congr]

#simplify eq env 0 (ite b x y)
end if_ctx_simp_congr

namespace if_congr_prop
constants {b c x y u v : Prop} (dec_b : decidable b) (dec_c : decidable c)
          (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v))

 attribute dec_b [instance]
 attribute dec_c [instance]
 attribute h_c [simp]
 attribute h_t [simp]
 attribute h_e [simp]

attribute if_ctx_congr_prop [congr]

#simplify iff env 0 (ite b x y)
end if_congr_prop

namespace if_ctx_simp_congr_prop
constants (b c x y u v : Prop) (dec_b : decidable b)
          (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬ c → (y ↔ v))

 attribute dec_b [instance]
 attribute h_c [simp]
 attribute h_t [simp]
 attribute h_e [simp]

attribute if_ctx_simp_congr_prop [congr]
#simplify iff env 0 (ite b x y)

end if_ctx_simp_congr_prop

namespace if_simp_congr_prop
constants (b c x y u v : Prop) (dec_b : decidable b)
          (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v)

 attribute dec_b [instance]
 attribute h_c [simp]
 attribute h_t [simp]
 attribute h_e [simp]

attribute if_simp_congr_prop [congr]
#simplify iff env 0 (ite b x y)
end if_simp_congr_prop
