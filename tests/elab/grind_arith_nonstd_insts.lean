module
class Distrib (R : Type _) extends Mul R where

namespace Nat

instance instDistrib : Distrib Nat where
  mul := (· * ·)

theorem odd_iff.extracted_1_4 {n : Nat} (m : Nat)
  (hm : n =
    @HMul.hMul _ _ _ (@instHMul Nat instDistrib.toMul)
      2 m + 1) :
    n % 2 = 1 := by
  grind

end Nat

namespace Int

instance instDistrib : Distrib Int where
  mul := (· * ·)

theorem four_dvd_add_or_sub_of_odd.extracted_1_1 (m n : Int) :
    4 ∣ ((@HMul.hMul Int Int Int (@instHMul Int Int.instDistrib.toMul)
          2 m) + 1) +
        ((@HMul.hMul Int Int Int (@instHMul Int Int.instDistrib.toMul)
          2 n) + 1) ∨
    4 ∣ ((@HMul.hMul Int Int Int (@instHMul Int Int.instDistrib.toMul)
          2 m) + 1) -
        ((@HMul.hMul Int Int Int (@instHMul Int Int.instDistrib.toMul)
          2 n) + 1) := by
  grind
