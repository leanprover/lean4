example (a b c : nat) (f : nat → nat → nat) (H₁ : a = b) (H₂ : b = c) : f (f a a) (f b b) = f (f c c) (f c c) :=
have h : a = c, from eq.trans H₁ H₂,
proof
  calc f (f a a) (f b b) = f (f c c) (f b b) : by rewrite h
                   ...   = f (f c c) (f c c) : by rewrite H₂
qed
