-- We can also use Lean simplifier to simplify proofs.

-- First, we prove some theorems about trans. All theorems are just using the fact that
-- we have proof irrelevance in Lean. That is, all proofs of a fact A are considered equal.
theorem trans_refl_right {A : TypeU} {a b : A} (Hab : a = b) (Hbb : b = b) : trans Hab Hbb = Hab
:= proof_irrel (trans Hab Hbb) Hab

theorem trans_refl_left {A : TypeU} {a b : A} (Haa : a = a) (Hab : a = b) : trans Haa Hab = Hab
:= proof_irrel (trans Haa Hab) Hab

theorem trans_assoc {A : TypeU} {a b c d : A} (Hab : a = b) (Hbc : b = c) (Hcd : c = d) :
         trans (trans Hab Hbc) Hcd = trans Hab (trans Hbc Hcd)
:= proof_irrel (trans (trans Hab Hbc) Hcd) (trans Hab (trans Hbc Hcd))

theorem symm_trans {A : TypeU} {a b c : A} (Hab : a = b) (Hbc : b = c) :
         symm (trans Hab Hbc) = trans (symm Hbc) (symm Hab)
:= proof_irrel (symm (trans Hab Hbc)) (trans (symm Hbc) (symm Hab))

-- Now, we define a new rewrite rule set for these theorems
rewrite_set proof_simp
add_rewrite trans_refl_right trans_refl_left trans_assoc symm_trans : proof_simp

-- Now, we create a simple example where a "messy" proof is simplified
variables a1 a2 a3 a4 : Nat
axiom Ax1 : a1 = a2
axiom Ax2 : a2 = a3
axiom Ax3 : a3 = a2
axiom Ax4 : a2 = a4

(*
local messy_proof = parse_lean("symm (trans (trans (trans (refl a1) (trans (trans Ax1 (refl a2)) Ax2)) (refl a3)) (trans Ax3 Ax4))")
print(messy_proof)
clean_proof, _ = simplify(messy_proof, 'proof_simp')
print(clean_proof)
*)
