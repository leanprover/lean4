section

  parameters x y : nat
  def z := x + y

  lemma h0 : z = y + x := add_comm _ _

  open tactic

  theorem foo₁ : z = y + x := -- doesn't work
  begin
   rw h0
  end

  theorem foo₂ : z = y + x := -- works
  by do rewrite `h0


  theorem foo₃ : z = y + x := -- doesn't work
  by rewrite h0

  theorem foo₄ : z = y + x := -- doesn't work
  begin
   simp [h0]
  end

  theorem foo₅ : z = y + x := -- doesn't work
  begin [smt]
    ematch_using [h0]
  end
end
