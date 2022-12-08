mutual
inductive A : Type
| a : A

inductive B : Type
| b : B
end

example (x : PSigma fun (a : A) => True) : A := by
  cases x with | mk x₁ x₂ => ?_
  induction x₁
  done
