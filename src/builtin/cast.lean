import heq

variable cast {A B : TypeM} : A = B → A → B

axiom cast_heq {A B : TypeM} (H : A = B) (a : A) : cast H a == a

theorem cast_app {A A' : TypeM} {B : A → TypeM} {B' : A' → TypeM} (f : ∀ x, B x) (a : A) (Ha : A = A') (Hb : (∀ x, B x) = (∀ x, B' x)) :
      cast Hb f (cast Ha a) == f a
:= let s1 : cast Hb f == f  := cast_heq Hb f,
       s2 : cast Ha a == a  := cast_heq Ha a
   in hcongr s1 s2

-- The following theorems can be used as rewriting rules

theorem cast_eq {A : TypeM} (H : A = A) (a : A) : cast H a = a
:= to_eq (cast_heq H a)

theorem cast_trans {A B C : TypeM} (Hab : A = B) (Hbc : B = C) (a : A) : cast Hbc (cast Hab a) = cast (trans Hab Hbc) a
:= let s1 : cast Hbc (cast Hab a)  == cast Hab a              :=  cast_heq Hbc (cast Hab a),
       s2 : cast Hab a             == a                       :=  cast_heq Hab a,
       s3 : cast (trans Hab Hbc) a == a                       :=  cast_heq (trans Hab Hbc) a,
       s4 : cast Hbc (cast Hab a)  == cast (trans Hab Hbc) a  :=  htrans (htrans s1 s2) (hsymm s3)
   in to_eq s4

theorem cast_pull {A : TypeM} {B B' : A → TypeM} (f : ∀ x, B x) (a : A) (Hb : (∀ x, B x) = (∀ x, B' x)) (Hba : (B a) = (B' a)) :
      cast Hb f a = cast Hba (f a)
:= let s1 : cast Hb f a    == f a    :=  hcongr (cast_heq Hb f) (hrefl a),
       s2 : cast Hba (f a) == f a    :=  cast_heq Hba (f a)
   in to_eq (htrans s1 (hsymm s2))
