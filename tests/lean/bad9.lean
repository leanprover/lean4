SetOption pp::implicit true.
SetOption pp::colors   false.
Variable N : Type.

Check
fun (a : N) (f : N -> N) (H : f a == a),
let calc1 : f a == a := SubstP (fun x : N, f a == _) (Refl (f a)) H
in  calc1.